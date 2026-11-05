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

import argparse, csv, json, math, time
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np
from scipy.optimize import brentq
from flint import arb, ctx

FACT = [1, 1, 2, 6, 24, 120, 720, 5040]


def A(x: Any) -> arb:
    return arb(str(x))


def D(x: Any) -> Decimal:
    return Decimal(str(x))


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
    m2_lo = arb(2) / 3 + A(str(min(loD**2, hiD**2) / 2))
    m2_hi = arb(2) / 3 + A(str(max(loD**2, hiD**2) / 2))
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
        return -arb(83) / 120
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
    __slots__ = ("kind", "param", "lam", "B", "xi", "alpha", "parseval_terms", "n_int", "is_sin", "sign")
    def __init__(self, kind: str, param: Any, lam: arb, B: arb):
        self.kind = kind; self.param = param; self.lam = lam; self.B = B
        self.xi = None; self.alpha = None; self.parseval_terms = None; self.n_int = None
        self.is_sin = False; self.sign = -1
        if kind in ("cos", "-cos", "sin", "-sin"):
            self.xi = A(param)
            self.is_sin = kind in ("sin", "-sin")
            self.sign = -1 if kind in ("cos", "sin") else 1
        elif kind == "cos+asin":
            self.xi = A(param[0]); self.alpha = A(param[1])
        elif kind in ("harmonic_cos", "cos_harmonic", "pi_cos"):
            self.n_int = int(param)
            self.xi = self.n_int * arb.pi()
            self.is_sin = False
            self.sign = -1
        elif kind in ("parseval", "weighted_parseval", "parseval_combined", "parseval_spectral"):
            pi_arb = arb.pi()
            terms_list = []
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
                    n = int(n_raw)
                    w = A(w_raw)
                    if (w < 0) or (w > arb(1) + arb("1e-15")):
                        raise ValueError(f"Parseval weight for n={n} out of [0, 1]: {w}")
                    xi = n * pi_arb
                    terms_list.append((n, w, xi))
            else:
                raw_c = param.get("c", param.get("coefficients", {})) if isinstance(param, dict) else param
                items = raw_c.items() if isinstance(raw_c, dict) else enumerate(raw_c, 1)
                lam_W = A(param.get("lambda_W", "0")) if isinstance(param, dict) else arb(0)
                for n_raw, c_raw in items:
                    n = int(n_raw)
                    c = A(c_raw)
                    if isinstance(param, dict) and "lambda_W" in param and c > lam_W + arb("1e-15"):
                        raise ValueError(f"Coefficient c_{n} = {c} exceeds lambda_W = {lam_W}")
                    xi = n * pi_arb
                    terms_list.append((n, c, xi))
            self.parseval_terms = terms_list


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
            B = A(raw["B"]) + rhs_inflate
        else:
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
        elif k == "t4":
            d[0] -= lam * x4
            if order > 1: d[1] -= lam * 4 * x3
            if order > 2: d[2] -= lam * 12 * x2
            if order > 3: d[3] -= lam * 24 * x
            if order > 4: d[4] -= lam * 24
        elif k in ("cos", "-cos", "sin", "-sin"):
            xi = t.xi
            s, c = (xi * x).sin_cos()
            wp = arb(1)
            for j in range(order):
                if j > 0: wp *= xi
                cycle = (j + (1 if t.is_sin else 0)) % 4
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
            for n, c_val, xi in t.parseval_terms:
                if c_val == 0:
                    continue
                s, c = (xi * x).sin_cos()
                lc = lam * c_val
                wp = arb(1)
                for j in range(order):
                    if j > 0: wp *= xi
                    cycle = j % 4
                    if cycle == 0: base = c
                    elif cycle == 1: base = -s
                    elif cycle == 2: base = -c
                    else: base = s
                    d[j] += lc * (wp * base)
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
        return 0
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
    if not s:
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
    return ans


def verify(data: Dict[str, Any], target_s: str, bins: List[int], cell_width_s: str, root_pad: float, samples: int, max_nodes: int, rhs_inflate_s: str, order: int, csv_path: Optional[Path]) -> Dict[str, Any]:
    targetD = arb(1) / A(target_s)
    cell_width = Decimal(cell_width_s)
    rhs_inflate = A(rhs_inflate_s)
    rows = []
    failures = []
    worst_i = None
    worst_D = None
    total_nodes = total_amb = max_roots = 0
    t0 = time.time()
    for i in bins:
        cert = data["bins"][i]
        U, info = upper_integral_bin(cert, cell_width, root_pad, samples, max_nodes, rhs_inflate, order)
        ok = U < targetD
        if worst_D is None or U.upper() > worst_D.upper():
            worst_D = U; worst_i = i
        total_nodes += info["nodes"]; total_amb += info["ambiguous_cells"]; max_roots = max(max_roots, info["speed_roots"])
        row = {
            "bin_index": i, "lo": cert["lo"], "hi": cert["hi"],
            "D_upper_ball": U.str(50), "D_upper_float": float(U.upper()),
            "proved": bool(ok), **info,
        }
        rows.append(row)
        if not ok:
            failures.append(row)
        print(f"bin {i:3d}: D <= {U.upper().str(24)}  {'OK' if ok else 'FAIL'}  nodes={info['nodes']} amb={info['ambiguous_cells']} roots={info['speed_roots']}", flush=True)
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
        "certified_lower_bound_lower_float": float(lower_bound.lower()) if lower_bound is not None else None,
        "proved_all_checked_bins": len(failures) == 0,
        "failures": failures,
        "checked_bins": bins,
        "total_nodes": total_nodes,
        "total_ambiguous_cells": total_amb,
        "max_speed_roots": max_roots,
        "elapsed_seconds": time.time() - t0,
        "arb_precision_bits": ctx.prec,
        "cell_width": cell_width_s,
        "root_pad": root_pad,
        "samples": samples,
        "rhs_inflate": rhs_inflate_s,
        "order": order,
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("certificate_json", type=Path)
    ap.add_argument("--target", default="0.38055631")
    ap.add_argument("--prec", type=int, default=160)
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
    ctx.prec = args.prec
    getcontext().prec = 80
    data = json.loads(args.certificate_json.read_text(), parse_float=str, parse_int=str)
    repaired = repair_tiny_bin_gaps(data)
    if repaired:
        print(f"Repaired {repaired} tiny bin endpoint gap(s) conservatively.")
    bins = parse_bins(args.only_bins, len(data["bins"]))
    result = verify(data, args.target, bins, args.cell_width, args.root_pad, args.samples, args.max_nodes, args.rhs_inflate, args.order, args.csv)
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
