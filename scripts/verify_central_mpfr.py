#!/usr/bin/env python3
"""Cross-check of the central window with the 192-bit MPFR verifier.

Compiles scripts/verify_quadrisected_mpfr.c and evaluates Deng's central
certificate (scripts/weighted_center_combined_038056070.txt) on the 32 chunks
of [0, 2] listed in scripts/weighted_038056070_center_manifest.csv. The
verifier uses the second-moment bound 2/3 + 1/3276800 of the window
|mean| <= 1/1280. The per-chunk upper bounds for the integral of max(0, q)
over the chunk are summed in exact rational arithmetic, and since the
certificate is even in x, D = 2 * (integral of max(0, q) over [0, 2]).
"""

import argparse
import csv
import re
import shutil
import subprocess
import sys
import tempfile
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "scripts" / "verify_quadrisected_mpfr.c"
COEFFS = ROOT / "scripts" / "weighted_center_combined_038056070.txt"
MANIFEST = ROOT / "scripts" / "weighted_038056070_center_manifest.csv"
DHALF = re.compile(r"^Dhalf_upper:\s*([0-9]+(?:\.[0-9]+)?)\s*$", re.M)


def decimal_fraction(value):
    number = Decimal(value)
    if not number.is_finite():
        raise ValueError("Certificate scalars must be finite decimals")
    return Fraction(number)


def units(value):
    scaled = decimal_fraction(value) * 10000
    if scaled.denominator != 1:
        raise ValueError(f"Chunk endpoint is not on the 1/10000 grid: {value}")
    return scaled.numerator


def validate_chunks(rows):
    chunks = sorted((units(r["lo"]), units(r["hi"]), r["lo"], r["hi"]) for r in rows)
    end = 0
    for lo, hi, _, _ in chunks:
        if lo != end or not lo < hi <= 20000:
            raise ValueError("Chunks must partition [0, 2] without gaps or overlaps")
        end = hi
    if end != 20000:
        raise ValueError("Chunks do not cover [0, 2]")
    return chunks


def validate_coefficients(path):
    lines = path.read_text().splitlines()
    if not lines or lines[0].split() != ["FORMAT", "weighted-center-coefficients-v1"]:
        raise ValueError("Unknown coefficient format")
    scalars, coefficients, cosines = {}, {}, []
    for line in lines[1:]:
        row = line.split()
        if not row:
            continue
        tag = row[0]
        if tag in ("T2", "WINDOW") and len(row) == 2:
            if tag in scalars:
                raise ValueError(f"Duplicate {tag} row")
            scalars[tag] = decimal_fraction(row[1])
        elif tag == "COS" and len(row) == 3:
            xi, lam = map(decimal_fraction, row[1:])
            if xi <= 0 or lam < 0:
                raise ValueError("COS frequencies must be positive and multipliers nonnegative")
            cosines.append((xi, lam))
        elif tag == "PI" and len(row) == 3:
            n = int(row[1])
            if n in coefficients or not 1 <= n <= 400:
                raise ValueError("PI indices must occur exactly once in 1..400")
            coefficients[n] = decimal_fraction(row[2])
        else:
            raise ValueError(f"Invalid coefficient row: {line}")
    if set(scalars) != {"T2", "WINDOW"} or len(cosines) != 80 or set(coefficients) != set(range(1, 401)):
        raise ValueError("Incomplete coefficient file")
    if scalars["T2"] < 0 or scalars["WINDOW"] < 0:
        raise ValueError("T2 and WINDOW multipliers must be nonnegative")
    if any(c > scalars["WINDOW"] for c in coefficients.values()):
        raise ValueError("Combined harmonic coefficient exceeds WINDOW")


def ceil_places(x, places):
    return Decimal(-((-x.numerator * 10**places) // x.denominator)).scaleb(-places)


def floor_places(x, places):
    return Decimal((x.numerator * 10**places) // x.denominator).scaleb(-places)


def compile_verifier(directory, mean_denominator=1280):
    compiler = shutil.which("gcc") or shutil.which("clang") or shutil.which("cc")
    if compiler is None:
        sys.exit("No C compiler found.")
    binary = Path(directory) / "verify_quadrisected_mpfr"
    subprocess.run(
        [compiler, "-O2", f"-DMEAN_DENOM={mean_denominator}", str(SOURCE), "-o", str(binary), "-lmpfr", "-lgmp", "-lm"],
        check=True,
    )
    return binary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mean-denominator", type=int, choices=(320, 512, 1280, 5120), default=1280)
    args = parser.parse_args()
    validate_coefficients(COEFFS)
    with open(MANIFEST, newline="") as f:
        chunks = validate_chunks(csv.DictReader(f))
    print(f"Validated coefficients and partition; central window |mean| <= 1/{args.mean_denominator}", flush=True)
    total = Fraction(0)
    with tempfile.TemporaryDirectory() as tmp:
        binary = compile_verifier(tmp, args.mean_denominator)
        for index, (lo, hi, lo_text, hi_text) in enumerate(chunks, 1):
            run = subprocess.run(
                [str(binary), str(COEFFS), str(lo), str(hi), "28"],
                capture_output=True,
                text=True,
            )
            match = DHALF.search(run.stdout)
            if run.returncode != 0 or "CHUNK_CERTIFIED True" not in run.stdout or match is None:
                sys.exit(f"Chunk {index} [{lo_text}, {hi_text}] failed.\n{run.stdout}\n{run.stderr}")
            value = Fraction(match.group(1))
            total += value
            if value < 0:
                sys.exit(f"Negative positive-part integral bound in chunk {index}")
            print(f"chunk {index:2d}/{len(chunks)}  [{lo_text}, {hi_text}]  upper bound {float(value):.12f}", flush=True)
    D = 2 * total
    if D <= 0:
        sys.exit("The integral bound must be positive")
    print(f"Central window only: |mean| <= 1/{args.mean_denominator}")
    print(f"D <= {ceil_places(D, 15)}")
    print(f"overlap supremum >= 1/D >= {floor_places(1 / D, 15)}")
    print(f"Rounded: D <= {ceil_places(D, 8)}, overlap supremum >= {floor_places(1 / D, 8)} within this window")


if __name__ == "__main__":
    main()
