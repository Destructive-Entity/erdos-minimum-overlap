#!/usr/bin/env python3
"""
Arb/ball-arithmetic verifier for the Erdős minimum-overlap certificate.

The script verifies the finite dual certificate

    q_I(t) = 1 + sum_j lambda_j (B_j - phi_j(t)),  lambda_j >= 0,

for each mean bin I.  For correctness, B_j is recomputed as an outward Arb upper
bound for the corresponding mathematical RHS; the stored B values are not trusted.
Floating-point root searches are used only to seed a subdivision.  Every interval
in the final subdivision is certified using Arb balls and the Taylor remainder majorant:
Order 2: q(x) <= q(c) + |q'(c)| r + M2 r^2 / 2
Order 4: q(x) <= q(c) + |q'(c)| r + |q''(c)| r^2 / 2 + |q'''(c)| r^3 / 6 + M4 r^4 / 24
"""
from __future__ import annotations

import argparse, csv, hashlib, json, math, time
from decimal import Decimal, getcontext
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor
from multiprocessing import get_context
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np
from scipy.optimize import brentq
from flint import arb, ctx

FACT = [1, 1, 2, 6, 24, 120, 720, 5040]


def A(x: Any) -> arb:
    return arb(str(D(x)))


def D(x: Any) -> Decimal:
    value = Decimal(str(x))
    if not value.is_finite():
        raise ValueError("Certificate scalars must be finite decimals")
    return value


def rational_ball(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def harmonic_index(value: Any) -> int:
    number = D(value)
    if number <= 0 or number != number.to_integral_value():
        raise ValueError(f"Harmonic index must be a positive integer: {value}")
    return int(number)


def upper(x: arb) -> arb:
    return x.upper()


def pos_upper(x: arb) -> arb:
    return arb(0) if x <= 0 else x.upper()


def sinc(x: arb) -> arb:
    if x.contains(arb(0)):
        return x.sinc()
    return x.sin() / x


def sqrt_max0_upper(x: arb) -> arb:
    if x <= 0:
        return arb(0)
    u = x.upper()
    if u <= 0:
        return arb(0)
    return u.sqrt()


def rhs_expected(kind: str, param: Any, lo: str, hi: str) -> Optional[arb]:
    loD, hiD = D(lo), D(hi)
    loQ, hiQ = Fraction(loD), Fraction(hiD)
    if loQ > hiQ:
        raise ValueError("Reversed mean interval")
    min_square = Fraction(0) if loQ <= 0 <= hiQ else min(loQ**2, hiQ**2)
    m2_lo = arb(2) / 3 + rational_ball(min_square / 2)
    m2_hi = arb(2) / 3 + rational_ball(max(loQ**2, hiQ**2) / 2)
    if kind == "t":
        return A(hi)
    if kind == "-t":
        return -A(lo)
    if kind == "t2":
        return m2_hi
    if kind == "-t2":
        return -m2_lo
    if kind == "t4":
        max_abs_mu = max(abs(loD), abs(hiD))
        return arb(16) / 15 + A(str(max_abs_mu))
    if kind == "-t4":
        return -arb(4) / 9
    if kind == "cos":
        s = sinc(A(param)); return s * s
    if kind == "-cos":
        s = sinc(A(param)); return arb(1) - 2 * s * s
    if kind in ("sin", "-sin"):
        s = sinc(A(param))
        return 2 * s.abs_upper() * sqrt_max0_upper(arb(1) - s * s)
    if kind == "cos+asin":
        xi, alpha = A(param[0]), A(param[1])
        s = sinc(xi)
        return (arb(1) + alpha * alpha) * s * s
    if kind in ("parseval", "weighted_parseval", "parseval_budget"):
        return arb(1) / 2
    if kind in ("harmonic_cos", "cos_harmonic", "pi_cos"):
        return arb(0)
    if kind in ("parseval_combined", "parseval_spectral"):
        if isinstance(param, dict):
            lam_W = A(param.get("lambda_W", "0"))
            return lam_W / 2
        return None
    return None


class Term:
    __slots__ = ("kind", "param", "lam", "B", "xi", "alpha", "parseval_terms", "parseval_derivatives", "n_int", "is_sin", "sign")
    def __init__(self, kind: str, param: Any, lam: arb, B: arb):
        self.kind = kind; self.param = param; self.lam = lam; self.B = B
        self.xi = None; self.alpha = None; self.parseval_terms = None; self.n_int = None
        self.is_sin = False; self.sign = -1
        if kind in ("cos", "-cos", "sin", "-sin"):
            if D(param) == 0:
                raise ValueError("Trigonometric frequencies must be nonzero")
            self.xi = A(param)
            self.is_sin = kind in ("sin", "-sin")
            self.sign = -1 if kind in ("cos", "sin") else 1
        elif kind == "cos+asin":
            if D(param[0]) == 0:
                raise ValueError("Trigonometric frequencies must be nonzero")
            self.xi = A(param[0]); self.alpha = A(param[1])
        elif kind in ("harmonic_cos", "cos_harmonic", "pi_cos"):
            self.n_int = harmonic_index(param)
            self.xi = self.n_int * arb.pi()
            self.is_sin = False
            self.sign = -1
        elif kind in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
            pi_arb = arb.pi()
            terms_list = []
            seen = set()
            if kind in ("parseval", "weighted_parseval"):
                if isinstance(param, dict):
                    raw_w = param.get("weights", param)
                    items = raw_w.items() if isinstance(raw_w, dict) else enumerate(raw_w, 1)
                elif isinstance(param, list):
                    if param and isinstance(param[0], (list, tuple)):
                        items = param
                    else:
                        items = enumerate(param, 1)
                else:
                    raise ValueError(f"Unknown param format for weighted_parseval: {param}")
                for n_raw, w_raw in items:
                    n = harmonic_index(n_raw)
                    if n in seen:
                        raise ValueError(f"Repeated Parseval harmonic: {n}")
                    seen.add(n)
                    if not 0 <= D(w_raw) <= 1:
                        raise ValueError(f"Parseval weight for n={n} out of [0, 1]: {w_raw}")
                    w = A(w_raw)
                    xi = n * pi_arb
                    terms_list.append((n, w, xi))
            else:
                if not isinstance(param, dict) or "lambda_W" not in param:
                    raise ValueError("Combined Parseval rows require lambda_W")
                raw_c = param.get("c", param.get("coefficients", {}))
                items = raw_c.items() if isinstance(raw_c, dict) else enumerate(raw_c, 1)
                lam_W = D(param["lambda_W"])
                if lam_W < 0:
                    raise ValueError("Parseval budget must be nonnegative")
                for n_raw, c_raw in items:
                    n = harmonic_index(n_raw)
                    if n in seen:
                        raise ValueError(f"Repeated Parseval harmonic: {n}")
                    seen.add(n)
                    if D(c_raw) > lam_W:
                        raise ValueError(f"Coefficient c_{n} = {c_raw} exceeds lambda_W = {lam_W}")
                    c = A(c_raw)
                    xi = n * pi_arb
                    terms_list.append((n, c, xi))
            self.parseval_terms = terms_list
            self.parseval_derivatives = []
            for _, c, xi in terms_list:
                coefficients = [lam * c]
                for _ in range(3):
                    coefficients.append(coefficients[-1] * xi)
                self.parseval_derivatives.append((xi, *coefficients))


def phi_float(kind: str, param: Any, x: float) -> float:
    if kind == "t": return x
    if kind == "-t": return -x
    if kind == "t2": return x*x
    if kind == "-t2": return -x*x
    if kind == "t4": return x*x*x*x
    if kind == "-t4": return -x*x*x*x
    if kind == "cos": return math.cos(float(param)*x)
    if kind == "-cos": return -math.cos(float(param)*x)
    if kind == "sin": return math.sin(float(param)*x)
    if kind == "-sin": return -math.sin(float(param)*x)
    if kind == "cos+asin":
        xi, alpha = float(param[0]), float(param[1])
        return math.cos(xi*x) + alpha*math.sin(xi*x)
    if kind in ("harmonic_cos", "cos_harmonic", "pi_cos"):
        return math.cos(int(param) * math.pi * x)
    if kind == "parseval_budget":
        return 0.0
    if kind in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
        if isinstance(param, list) and param and isinstance(param[0], tuple):
            return -math.fsum(c * math.cos(xi * x) for xi, c in param)
        items = []
        if kind in ("parseval", "weighted_parseval"):
            raw_w = param.get("weights", param) if isinstance(param, dict) else param
            it = raw_w.items() if isinstance(raw_w, dict) else enumerate(raw_w, 1)
            items = [(int(n) * math.pi, float(w)) for n, w in it if float(w)]
        else:
            raw_c = param.get("c", param.get("coefficients", {})) if isinstance(param, dict) else param
            it = raw_c.items() if isinstance(raw_c, dict) else enumerate(raw_c, 1)
            items = [(int(n) * math.pi, float(c)) for n, c in it if float(c)]
        return -math.fsum(c * math.cos(xi * x) for xi, c in items)
    raise ValueError(kind)


def phi_vec(kind: str, param: Any, x: np.ndarray) -> np.ndarray:
    if kind == "t": return x
    if kind == "-t": return -x
    if kind == "t2": return x*x
    if kind == "-t2": return -x*x
    if kind == "t4": return x*x*x*x
    if kind == "-t4": return -x*x*x*x
    if kind == "cos": return np.cos(float(param)*x)
    if kind == "-cos": return -np.cos(float(param)*x)
    if kind == "sin": return np.sin(float(param)*x)
    if kind == "-sin": return -np.sin(float(param)*x)
    if kind == "cos+asin":
        xi, alpha = float(param[0]), float(param[1])
        return np.cos(xi*x) + alpha*np.sin(xi*x)
    if kind in ("harmonic_cos", "cos_harmonic", "pi_cos"):
        return np.cos(int(param) * math.pi * x)
    if kind == "parseval_budget":
        return np.zeros_like(x)
    if kind in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
        items = []
        if isinstance(param, list) and param and isinstance(param[0], tuple):
            items = param
        elif kind in ("parseval", "weighted_parseval"):
            raw_w = param.get("weights", param) if isinstance(param, dict) else param
            it = raw_w.items() if isinstance(raw_w, dict) else enumerate(raw_w, 1)
            items = [(int(n) * math.pi, float(w)) for n, w in it if float(w)]
        else:
            raw_c = param.get("c", param.get("coefficients", {})) if isinstance(param, dict) else param
            it = raw_c.items() if isinstance(raw_c, dict) else enumerate(raw_c, 1)
            items = [(int(n) * math.pi, float(c)) for n, c in it if float(c)]
        out = np.zeros_like(x)
        for xi, c in items:
            out += c * np.cos(xi * x)
        return -out
    raise ValueError(kind)


def prepare_bin(cert: Dict[str, Any], rhs_inflate: arb, order: int = 4) -> Tuple[List[Term], List[Tuple[str, Any, float, float]], arb, int]:
    if not rhs_inflate.is_finite() or not rhs_inflate >= 0:
        raise ValueError("RHS inflation must be nonnegative and finite")
    if order not in (2, 4):
        raise ValueError("Taylor order must be 2 or 4")
    terms: List[Term] = []
    fterms: List[Tuple[str, Any, float, float]] = []
    Mk = arb(0)
    adjusted = 0
    k = order
    for j, raw in enumerate(cert["active"]):
        kind, param = raw["kind"], raw.get("param")
        if D(raw["lambda"]) < 0:
            raise ValueError(f"negative multiplier in bin {cert['lo']},{cert['hi']} term {j}")
        lam = A(raw["lambda"])
        e = rhs_expected(kind, param, cert["lo"], cert["hi"])
        if e is None:
            raise ValueError(f"No proved RHS for constraint kind {kind}")
        B = e.upper() + rhs_inflate
        adjusted += 1
        t_obj = Term(kind, param, lam, B)
        terms.append(t_obj)
        if kind in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
            f_param = [(int(n) * math.pi, float(c)) for n, c, xi in t_obj.parseval_terms if abs(float(c)) > 1e-12]
            fterms.append((kind, f_param, float(raw["lambda"]), float(B)))
        else:
            fterms.append((kind, param, float(raw["lambda"]), float(B)))
        # global bound for k-th derivative remainder
        lu = lam.abs_upper()
        if kind in ("t", "-t"):
            pass
        elif kind in ("t2", "-t2"):
            if k == 2:
                Mk += 2 * lu
        elif kind in ("t4", "-t4"):
            if k == 2:
                Mk += 48 * lu
            elif k == 3:
                Mk += 24 * lu
            elif k == 4:
                Mk += 24 * lu
        elif kind in ("cos", "-cos", "sin", "-sin"):
            xi = A(param)
            Mk += lu * (xi.abs_upper() ** k)
        elif kind == "cos+asin":
            xi, alpha = A(param[0]), A(param[1])
            amp = (arb(1) + alpha * alpha).sqrt()
            Mk += lu * (xi.abs_upper() ** k) * amp.abs_upper()
        elif kind in ("harmonic_cos", "cos_harmonic", "pi_cos"):
            xi = t_obj.xi
            Mk += lu * (xi.abs_upper() ** k)
        elif kind == "parseval_budget":
            pass
        elif kind in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
            cur_mk = arb(0)
            for n, c, xi in t_obj.parseval_terms:
                cur_mk += c.abs_upper() * (xi.abs_upper() ** k)
            Mk += lu * cur_mk
        else:
            raise ValueError(f"unknown term kind {kind}")
    return terms, fterms, Mk.upper(), adjusted


def q_float(fterms: Sequence[Tuple[str, Any, float, float]], x: float) -> float:
    parts = [1.0]
    for kind, param, lam, B in fterms:
        if lam:
            parts.append(lam * (B - phi_float(kind, param, x)))
    return math.fsum(parts)


def q_vec(fterms: Sequence[Tuple[str, Any, float, float]], x: np.ndarray) -> np.ndarray:
    out = np.ones_like(x, dtype=float)
    for kind, param, lam, B in fterms:
        if lam:
            out += lam * (B - phi_vec(kind, param, x))
    return out


def speed_roots(fterms: Sequence[Tuple[str, Any, float, float]], samples: int) -> List[float]:
    if samples <= 1:
        return []
    xs = np.linspace(-2.0, 2.0, samples)
    ys = q_vec(fterms, xs)
    roots: List[float] = []
    for i in range(samples - 1):
        fa, fb = float(ys[i]), float(ys[i+1])
        if fa == 0.0:
            roots.append(float(xs[i]))
        elif fa * fb < 0.0:
            try:
                roots.append(brentq(lambda z: q_float(fterms, z), float(xs[i]), float(xs[i+1]), xtol=1e-14, rtol=1e-14, maxiter=100))
            except Exception:
                pass
    if float(ys[-1]) == 0.0:
        roots.append(2.0)
    roots.sort()
    out: List[float] = []
    for r in roots:
        if not out or abs(r - out[-1]) > 1e-8:
            out.append(r)
    return out


def initial_intervals(roots: Sequence[float], pad: float) -> List[Tuple[str, str]]:
    if not roots:
        return [("-2.0", "2.0")]
    ans: List[Tuple[str, str]] = []
    last = -2.0
    for r in roots:
        a, b = max(-2.0, r - pad), min(2.0, r + pad)
        if a > last:
            ans.append((repr(last), repr(a)))
        if b > a:
            ans.append((repr(a), repr(b)))
        last = max(last, b)
    if last < 2.0:
        ans.append((repr(last), "2.0"))
    return ans


def q_derivs(terms: Sequence[Term], x: arb, order: int = 4) -> List[arb]:
    d = [arb(0) for _ in range(order)]
    d[0] = arb(1)
    x2 = x*x
    x3 = x2*x
    x4 = x2*x2
    for t in terms:
        lam = t.lam
        if lam == 0:
            continue
        d[0] += lam * t.B
        k = t.kind
        if k == "t":
            d[0] -= lam * x
            if order > 1: d[1] -= lam
        elif k == "-t":
            d[0] += lam * x
            if order > 1: d[1] += lam
        elif k == "t2":
            d[0] -= lam * x2
            if order > 1: d[1] -= lam * 2 * x
            if order > 2: d[2] -= lam * 2
        elif k == "-t2":
            d[0] += lam * x2
            if order > 1: d[1] += lam * 2 * x
            if order > 2: d[2] += lam * 2
        elif k in ("t4", "-t4"):
            signed_lam = -lam if k == "t4" else lam
            d[0] += signed_lam * x4
            if order > 1: d[1] += signed_lam * 4 * x3
            if order > 2: d[2] += signed_lam * 12 * x2
            if order > 3: d[3] += signed_lam * 24 * x
            if order > 4: d[4] += signed_lam * 24
        elif k in ("cos", "-cos", "sin", "-sin"):
            xi = t.xi
            s, c = (xi * x).sin_cos()
            wp = arb(1)
            for j in range(order):
                if j > 0: wp *= xi
                cycle = (j + (3 if t.is_sin else 0)) % 4
                if cycle == 0: base = c
                elif cycle == 1: base = -s
                elif cycle == 2: base = -c
                else: base = s
                d[j] += lam * (t.sign * wp * base)
        elif k == "cos+asin":
            xi, alpha = t.xi, t.alpha
            s, c = (xi * x).sin_cos()
            wp = arb(1)
            for j in range(order):
                if j > 0: wp *= xi
                cycle = j % 4
                if cycle == 0: base = c + alpha * s
                elif cycle == 1: base = -s + alpha * c
                elif cycle == 2: base = -c - alpha * s
                else: base = s - alpha * c
                d[j] -= lam * (wp * base)
        elif k in ("harmonic_cos", "cos_harmonic", "pi_cos"):
            xi = t.xi
            s, c = (xi * x).sin_cos()
            wp = arb(1)
            for j in range(order):
                if j > 0: wp *= xi
                cycle = j % 4
                if cycle == 0: base = c
                elif cycle == 1: base = -s
                elif cycle == 2: base = -c
                else: base = s
                d[j] -= lam * (wp * base)
        elif k == "parseval_budget":
            pass
        elif k in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
            for xi, c0, c1, c2, c3 in t.parseval_derivatives:
                if c0 == 0:
                    continue
                sine, cosine = (xi * x).sin_cos()
                d[0] += c0 * cosine
                if order > 1: d[1] -= c1 * sine
                if order > 2: d[2] -= c2 * cosine
                if order > 3: d[3] += c3 * sine
        else:
            raise ValueError(k)
    return d


def Q(terms: Sequence[Term], x: arb) -> arb:
    val = x
    for t in terms:
        lam = t.lam
        if lam == 0:
            continue
        k = t.kind
        val += lam * t.B * x
        if k == "t":
            anti = x*x/2
        elif k == "-t":
            anti = -x*x/2
        elif k == "t2":
            anti = x*x*x/3
        elif k == "-t2":
            anti = -x*x*x/3
        elif k == "t4":
            anti = (x*x*x*x*x)/5
        elif k == "-t4":
            anti = -(x*x*x*x*x)/5
        elif k in ("cos", "-cos", "sin", "-sin"):
            xi = t.xi
            s, c = (xi * x).sin_cos()
            if k == "cos":
                anti = s / xi
            elif k == "-cos":
                anti = -s / xi
            elif k == "sin":
                anti = -c / xi
            else:
                anti = c / xi
        elif k == "cos+asin":
            xi, alpha = t.xi, t.alpha
            s, c = (xi * x).sin_cos()
            anti = s / xi - alpha * c / xi
        elif k in ("harmonic_cos", "cos_harmonic", "pi_cos"):
            xi = t.xi
            s = (xi * x).sin()
            anti = s / xi
        elif k == "parseval_budget":
            anti = arb(0)
        elif k in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
            anti = arb(0)
            for n, c, xi in t.parseval_terms:
                if c == 0:
                    continue
                s = (xi * x).sin()
                anti -= c * s / xi
        else:
            raise ValueError(k)
        val -= lam * anti
    return val


def upper_integral_bin(cert: Dict[str, Any], cell_width: Decimal, root_pad: float, samples: int, max_nodes: int, rhs_inflate: arb, order: int = 4) -> Tuple[arb, Dict[str, Any]]:
    terms, fterms, Mk, adjusted = prepare_bin(cert, rhs_inflate, order)
    roots = speed_roots(fterms, samples)
    stack = initial_intervals(roots, root_pad)
    Dtot = arb(0)
    nodes = amb = pos = neg = 0
    while stack:
        a_s, b_s = stack.pop()
        aD, bD = Decimal(a_s), Decimal(b_s)
        if bD <= aD:
            continue
        nodes += 1
        if nodes > max_nodes:
            raise RuntimeError(f"max_nodes exceeded in bin [{cert['lo']},{cert['hi']}]")
        a, b = A(a_s), A(b_s)
        c, r = (a+b)/2, (b-a)/2

        ds = q_derivs(terms, c, order)
        rad = arb(0)
        rp = arb(1)
        for j in range(1, order):
            rp *= r
            rad += ds[j].abs_upper() * rp / FACT[j]
        rp *= r
        rad += Mk * rp / FACT[order]

        lo, hi = ds[0] - rad, ds[0] + rad
        if hi <= 0:
            neg += 1
            continue
        if lo >= 0:
            Dtot += pos_upper(Q(terms, b) - Q(terms, a))
            pos += 1
            continue
        if bD - aD <= cell_width:
            Dtot += (b-a) * pos_upper(hi)
            amb += 1
            continue
        mD = (aD + bD) / 2
        m_s = format(mD, "f")
        stack.append((m_s, b_s)); stack.append((a_s, m_s))
    info = {
        "nodes": nodes,
        "ambiguous_cells": amb,
        "positive_cells": pos,
        "negative_cells": neg,
        "speed_roots": len(roots),
        "rhs_adjusted": adjusted,
        "Mk": Mk.str(30),
        "order": order,
    }
    return Dtot, info


def repair_tiny_bin_gaps(data: Dict[str, Any], max_gap: Decimal = Decimal("1e-12")) -> int:
    bins = data["bins"]
    if not bins:
        raise ValueError("The mean-bin cover is empty")
    if "nbins" in data and int(data["nbins"]) != len(bins):
        raise ValueError("Declared bin count does not match the certificate")
    previous_lo = Decimal("-1")
    for cert in bins:
        lo, hi = D(cert["lo"]), D(cert["hi"])
        if not Decimal("-1") <= lo < hi <= Decimal("1") or lo < previous_lo:
            raise ValueError("Mean bins must be ordered nonempty subintervals of [-1, 1]")
        previous_lo = lo
    changed = 0
    lo0 = D(bins[0]["lo"])
    if lo0 > Decimal("-1"):
        gap = lo0 - Decimal("-1")
        if gap <= max_gap:
            bins[0]["lo"] = "-1"
            changed += 1
        else:
            raise ValueError(f"initial uncovered mean gap: {gap}")
    prev = D(bins[0]["hi"])
    for i in range(1, len(bins)):
        lo = D(bins[i]["lo"])
        if lo > prev:
            gap = lo - prev
            if gap <= max_gap:
                bins[i]["lo"] = format(prev, "f")
                changed += 1
            else:
                raise ValueError(f"uncovered mean gap before bin {i}: {gap}")
        hi = D(bins[i]["hi"])
        if hi > prev:
            prev = hi
    if prev < Decimal("1"):
        gap = Decimal("1") - prev
        if gap <= max_gap:
            bins[-1]["hi"] = "1"; changed += 1
        else:
            raise ValueError(f"final uncovered mean gap: {gap}")
    return changed


def parse_bins(s: Optional[str], n: int) -> List[int]:
    if s is None:
        return list(range(n))
    ans: List[int] = []
    for part in s.split(','):
        part = part.strip()
        if not part:
            continue
        if '-' in part:
            a, b = part.split('-', 1)
            ans.extend(range(int(a), int(b)+1))
        else:
            ans.append(int(part))
    if not ans or len(set(ans)) != len(ans) or any(i < 0 or i >= n for i in ans):
        raise ValueError("Select distinct, in-range bin indices")
    return ans


def verify_bin_worker(argument):
    index, cert, settings = argument
    precision, cell_width, root_pad, samples, max_nodes, rhs_inflate, order = settings
    ctx.prec = precision
    getcontext().prec = 80
    bound, info = upper_integral_bin(cert, D(cell_width), root_pad, samples,
                                     max_nodes, A(rhs_inflate), order)
    return index, bound.upper().str(70), info


def verify(data: Dict[str, Any], target_s: str, bins: List[int], cell_width_s: str, root_pad: float, samples: int, max_nodes: int, rhs_inflate_s: str, order: int, csv_path: Optional[Path], jobs: int = 1) -> Dict[str, Any]:
    if not bins or len(set(bins)) != len(bins) or any(i < 0 or i >= len(data["bins"]) for i in bins):
        raise ValueError("Select distinct, in-range bin indices")
    if D(target_s) <= 0 or D(cell_width_s) <= 0 or D(rhs_inflate_s) < 0:
        raise ValueError("Target and cell width must be positive; RHS inflation must be nonnegative")
    if not math.isfinite(root_pad) or root_pad < 0 or samples < 0 or max_nodes <= 0:
        raise ValueError("Invalid subdivision parameters")
    if jobs < 1:
        raise ValueError("The worker count must be positive")
    targetD = arb(1) / A(target_s)
    rows = []
    failures = []
    worst_i = None
    worst_D = None
    total_nodes = total_amb = max_roots = 0
    t0 = time.time()
    settings = (ctx.prec, cell_width_s, root_pad, samples, max_nodes, rhs_inflate_s, order)
    arguments = ((i, data["bins"][i], settings) for i in bins)
    executor = ProcessPoolExecutor(max_workers=jobs, mp_context=get_context("spawn")) if jobs > 1 else None
    results = executor.map(verify_bin_worker, arguments) if executor else map(verify_bin_worker, arguments)
    try:
        for i, bound_text, info in results:
            cert = data["bins"][i]
            U = arb(bound_text)
            if not U.is_finite() or not U > 0:
                raise ValueError(f"Nonpositive or nonfinite integral bound for bin {i}")
            ok = U < targetD
            if worst_D is None or U.upper() > worst_D.upper():
                worst_D = U; worst_i = i
            total_nodes += info["nodes"]; total_amb += info["ambiguous_cells"]; max_roots = max(max_roots, info["speed_roots"])
            row = {
                "bin_index": i, "lo": cert["lo"], "hi": cert["hi"],
                "D_upper_ball": U.str(50), "D_upper_float": math.nextafter(float(U.upper()), math.inf),
                "proved": bool(ok), **info,
            }
            rows.append(row)
            if not ok:
                failures.append(row)
            print(f"bin {i:3d}: D <= {U.upper().str(24)}  {'OK' if ok else 'FAIL'}  nodes={info['nodes']} amb={info['ambiguous_cells']} roots={info['speed_roots']}", flush=True)
    finally:
        if executor:
            executor.shutdown()
    if csv_path and rows:
        with csv_path.open('w', newline='') as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader(); w.writerows(rows)
    lower_bound = arb(1) / worst_D if worst_D is not None else None
    return {
        "target": target_s,
        "target_D": targetD.str(60),
        "worst_bin_index": worst_i,
        "worst_bin": [data["bins"][worst_i]["lo"], data["bins"][worst_i]["hi"]] if worst_i is not None else None,
        "worst_D_upper_ball": worst_D.upper().str(60) if worst_D is not None else None,
        "certified_lower_bound_ball": lower_bound.str(60) if lower_bound is not None else None,
        "certified_lower_bound_lower_float": math.nextafter(float(lower_bound.lower()), -math.inf) if lower_bound is not None else None,
        "proved_all_checked_bins": len(failures) == 0,
        "proved_all_bins": len(failures) == 0 and set(bins) == set(range(len(data["bins"]))),
        "failures": failures,
        "checked_bins": bins,
        "total_nodes": total_nodes,
        "total_ambiguous_cells": total_amb,
        "max_speed_roots": max_roots,
        "elapsed_seconds": time.time() - t0,
        "arb_precision_bits": ctx.prec,
        "jobs": jobs,
        "cell_width": cell_width_s,
        "root_pad": root_pad,
        "samples": samples,
        "rhs_inflate": rhs_inflate_s,
        "order": order,
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("certificate_json", type=Path)
    ap.add_argument("--target", default="0.38056171")
    ap.add_argument("--prec", type=int, default=160)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--order", type=int, default=4, choices=[2, 4])
    ap.add_argument("--cell-width", default="0.00003")
    ap.add_argument("--root-pad", type=float, default=1e-4)
    ap.add_argument("--samples", type=int, default=120001)
    ap.add_argument("--max-nodes", type=int, default=50000000)
    ap.add_argument("--rhs-inflate", default="1e-14")
    ap.add_argument("--only-bins", default=None)
    ap.add_argument("--csv", type=Path)
    ap.add_argument("--json-report", type=Path)
    args = ap.parse_args(argv)
    if args.prec < 64:
        ap.error("--prec must be at least 64 bits")
    ctx.prec = args.prec
    getcontext().prec = 80
    data = json.loads(args.certificate_json.read_text(), parse_float=str, parse_int=str)
    repaired = repair_tiny_bin_gaps(data)
    if repaired:
        print(f"Repaired {repaired} tiny bin endpoint gap(s) conservatively.")
    bins = parse_bins(args.only_bins, len(data["bins"]))
    result = verify(data, args.target, bins, args.cell_width, args.root_pad, args.samples, args.max_nodes, args.rhs_inflate, args.order, args.csv, args.jobs)
    result["certificate_sha256"] = hashlib.sha256(args.certificate_json.read_bytes()).hexdigest()
    result["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.json_report:
        args.json_report.write_text(json.dumps(result, indent=2, ensure_ascii=False))
    print("\nArb verification summary")
    for k in ["target", "target_D", "worst_D_upper_ball", "certified_lower_bound_ball", "worst_bin_index", "worst_bin", "total_nodes", "total_ambiguous_cells", "max_speed_roots", "elapsed_seconds", "arb_precision_bits", "order"]:
        print(f"  {k}: {result[k]}")
    if result["proved_all_checked_bins"]:
        print("SUCCESS: every checked bin certifies the target.")
        return 0
    print("FAILED bins:")
    for row in result["failures"][:20]:
        print(row)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
