#!/usr/bin/env python3
"""Minimal sub-ULP admissibility repair for an Erdos min-overlap board vector.

Some board vectors clear the EinsteinArena verifier without being *exactly*
admissible: the verifier tests ``float(np.sum(f)) == n/2`` in binary64, which
rounds a vector whose exact rational sum is within half an ULP of ``n/2`` (at
the scale of ``n/2``) up (or down) to exactly ``n/2``.  A *proven* bound on the
minimum-overlap constant mu requires an f that is admissible in exact
arithmetic: entries in [0,1] and sum EXACTLY n/2.

This module supplies the minimal, deterministic repair for the *deficit* case
(exact sum slightly BELOW n/2), which is the interesting one: the board's own
uniform rescale ``f <- f*(n/2)/sum`` would multiply every entry UP by a factor
> 1 and push any box-saturated (value==1) cell above 1, breaking admissibility
-- and, historically, making the exact score strictly worse.  Instead we add
the exact integer deficit to the lowest-index cells that still have headroom
below 1.  Because the added mass is far below one ULP at the sum's scale and
placed in low-value cells whose contribution to the maximizing correlation is
negligible (bounded by the deficit itself), the board score is unchanged to
full float precision, while the vector becomes exactly admissible and yields a
genuine proven bound.

Everything on the certified path is exact (``fractions`` / integers only).
The optional float board-score cross-check uses numpy purely to demonstrate
that raw and repaired vectors receive a bit-identical board score; it plays no
role in the proof.

Usage:
    python3 repair_admissibility.py <raw_values.json>   [--out repaired.json]

``<raw_values.json>`` is any JSON with a top-level ``"values"`` list of the raw
board doubles (extra keys such as a stored ``repair_delta`` are checked when
present).  Prints the repair delta, the bit-identical float board scores, and
the exact repaired rational bound with its 25-digit round-up.
"""
import json
import sys
from fractions import Fraction

DIGITS = 25


def require(cond, msg):
    """Hard validation gate on the certified path.

    An explicit ``raise`` (never ``assert``), so it cannot be stripped by
    ``python -O`` / ``PYTHONOPTIMIZE=1``: these checks are load-bearing for
    the soundness of every certified bound.
    """
    if not cond:
        raise SystemExit("FATAL: " + msg)


def dyadic_ints(vals):
    """Exact common-power-of-two representation of a list of binary64 values.

    Returns (A, L) with each value == A_i / 2**L exactly and every A_i integer.
    """
    fr = [Fraction(v) for v in vals]
    require(all(0 <= x <= 1 for x in fr), "raw vector leaves [0,1]")
    Ls = []
    for x in fr:
        q = x.denominator
        l = q.bit_length() - 1
        require(q == (1 << l), "value is not an exact dyadic rational")
        Ls.append(l)
    L = max(Ls)
    A = [x.numerator << (L - l) for x, l in zip(fr, Ls)]
    return A, L


def minimal_repair(A, L):
    """Greedy minimal-deficit repair.

    Adds the exact integer deficit ``(n/2)*2**L - sum(A)`` to the lowest-index
    cells with headroom below 2**L.  Returns (A_repaired, deficit, mods) where
    ``mods`` is a list of ``[cell_index, integer_units_added]``.  Raises if the
    exact sum is not strictly below n/2 (the deficit case).
    """
    n = len(A)
    cap = 1 << L
    target = (n // 2) * cap
    deficit = target - sum(A)
    if deficit == 0:
        return A[:], 0, []
    if deficit < 0:
        raise ValueError(
            "exact sum is ABOVE n/2 (surplus %d units): this is the rescale case, "
            "handled by exact uniform shrink, not by this deficit repair." % (-deficit)
        )
    A2 = A[:]
    rem = deficit
    mods = []
    for i in range(n):
        if rem <= 0:
            break
        room = cap - A2[i]
        if room > 0:
            add = min(room, rem)
            A2[i] += add
            rem -= add
            mods.append([i, add])
    require(rem == 0, "could not place the deficit within available headroom")
    require(sum(A2) == target, "repaired sum is not exactly n/2")
    require(all(0 <= a <= cap for a in A2), "repaired vector leaves [0,1]")
    return A2, deficit, mods


def exact_score(A, L):
    """Exact sup_x M(x) = (2/n) * max_m sum_i A_i (2**L - A_{i+m}) / 2**(2L).

    Integer correlation; no floating point.  Returns (Fraction score, argmax m).
    """
    n = len(A)
    cap = 1 << L
    G = [cap - a for a in A]
    best_t, best_m = None, None
    for m in range(-(n - 1), n):
        lo, hi = max(0, -m), min(n, n - m)
        t = sum(A[i] * G[i + m] for i in range(lo, hi))
        if best_t is None or t > best_t:
            best_t, best_m = t, m
    score = Fraction(2, n) * Fraction(best_t, cap * cap)
    return score, best_m


def _fmt(ip):
    s = str(ip).rjust(DIGITS + 1, "0")
    return s[:-DIGITS] + "." + s[-DIGITS:]


def fmt_down(score):
    p, q = score.numerator, score.denominator
    return _fmt((p * 10 ** DIGITS) // q)


def fmt_up(score):
    p, q = score.numerator, score.denominator
    return _fmt(-((-(p * 10 ** DIGITS)) // q))


def board_score_float(vals):
    """Replicate the EinsteinArena float scorer exactly (needs numpy)."""
    import numpy as np

    f = np.array(vals, dtype=np.float64)
    if np.any(f < 0) or np.any(f > 1):
        raise AssertionError("value out of [0,1]")
    target = len(f) / 2.0
    s = float(np.sum(f))
    if s != target:                       # the board's rescale gate
        f = f * (target / s)
        if np.any(f < 0) or np.any(f > 1):
            raise AssertionError("post-rescale out of [0,1]")
    g = 1.0 - f
    return float(np.max(np.correlate(f, g, mode="full")) / len(f) * 2)


def repaired_values(A2, L):
    cap = 1 << L
    return [float(Fraction(a, cap)) for a in A2]


def main():
    if not __debug__:
        raise SystemExit("refusing to run under -O: validation is load-bearing")
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    path = sys.argv[1]
    obj = json.load(open(path))
    vals = obj["values"]
    n = len(vals)
    A, L = dyadic_ints(vals)
    cap = 1 << L
    raw_sum = Fraction(sum(A), cap)
    half = Fraction(n, 2)
    print(f"n = {n}   common denominator 2^{L}")
    print(f"raw exact sum(f) - n/2 = {float(raw_sum - half):.6e}"
          f"  ({'BELOW n/2 (deficit)' if raw_sum < half else 'ABOVE n/2 (surplus)' if raw_sum > half else 'EXACT'})")
    print(f"saturated cells (value == 1): {sum(1 for a in A if a == cap)}")

    A2, deficit, mods = minimal_repair(A, L)
    print(f"\nexact deficit = {deficit} units of 2^-{L}  = {float(Fraction(deficit, cap)):.6e}")
    print(f"minimal repair delta (cell_index, integer_units_added): {mods}")
    print(f"  -> touches {len(mods)} cell(s); sum now EXACTLY n/2 = {n // 2}, all entries in [0,1]")

    # cross-check against a stored repair_delta if the cert carries one
    if "repair_delta" in obj:
        stored = [list(x) for x in obj["repair_delta"]]
        require(stored == mods, f"stored repair_delta {stored} != recomputed {mods}")
        print("  stored repair_delta matches the independently recomputed delta.  OK")

    # exact scores (stdlib only)
    sc_raw, m_raw = exact_score(A, L)
    sc_rep, m_rep = exact_score(A2, L)
    print(f"\nRAW      exact score = {float(sc_raw):.17g}   (argmax lag {m_raw};  NOT admissible: sum != n/2)")
    print(f"REPAIRED exact score = {float(sc_rep):.17g}   (argmax lag {m_rep};  admissible)")
    print(f"  x* = 2*m*/n = {Fraction(2 * m_rep, n)} = {float(Fraction(2 * m_rep, n)):+.6f}")
    print(f"  exact bound  mu <= {sc_rep.numerator}/{sc_rep.denominator}")
    print(f"  decimal enclosure ({DIGITS} digits): {fmt_down(sc_rep)}  <=  bound  <  {fmt_up(sc_rep)}")
    print(f"  RIGOROUS: mu <= {fmt_up(sc_rep)}")

    # optional float board-score cross-check: raw vs repaired must be bit-identical
    try:
        b_raw = board_score_float(vals)
        b_rep = board_score_float(repaired_values(A2, L))
        same = (b_raw == b_rep)
        print(f"\nfloat board score  raw = {b_raw!r}")
        print(f"float board score  rep = {b_rep!r}")
        print(f"  raw == repaired board score (bit-identical)?  {same}")
        if not same:
            print("  WARNING: board scores differ -- repair changed the float score!")
            sys.exit(1)
    except ImportError:
        print("\n(numpy unavailable -- float board-score cross-check skipped; "
              "it plays no role in the proof)")

    if "--out" in sys.argv:
        out = sys.argv[sys.argv.index("--out") + 1]
        json.dump({"values": repaired_values(A2, L),
                   "denom_exp": L,
                   "repair_delta": mods,
                   "source": path},
                  open(out, "w"))
        print(f"\nwrote repaired admissible vector -> {out}")


if __name__ == "__main__":
    main()
