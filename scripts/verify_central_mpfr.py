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


def units(value):
    return int(Decimal(value) * 10000)


def ceil_places(x, places):
    return Decimal(-((-x.numerator * 10**places) // x.denominator)).scaleb(-places)


def floor_places(x, places):
    return Decimal((x.numerator * 10**places) // x.denominator).scaleb(-places)


def compile_verifier(directory):
    compiler = shutil.which("gcc") or shutil.which("clang") or shutil.which("cc")
    if compiler is None:
        sys.exit("No C compiler found.")
    binary = Path(directory) / "verify_quadrisected_mpfr"
    subprocess.run(
        [compiler, "-O2", str(SOURCE), "-o", str(binary), "-lmpfr", "-lgmp", "-lm"],
        check=True,
    )
    return binary


def main():
    with open(MANIFEST, newline="") as f:
        chunks = sorted(
            (units(r["lo"]), units(r["hi"]), r["lo"], r["hi"]) for r in csv.DictReader(f)
        )
    total = Fraction(0)
    with tempfile.TemporaryDirectory() as tmp:
        binary = compile_verifier(tmp)
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
            print(f"chunk {index:2d}/{len(chunks)}  [{lo_text}, {hi_text}]  upper bound {float(value):.12f}")
    D = 2 * total
    print(f"D <= {ceil_places(D, 15)}")
    print(f"mu >= 1/D >= {floor_places(1 / D, 15)}")
    print(f"Rounded: D <= {ceil_places(D, 8)}, mu >= {floor_places(1 / D, 8)}")


if __name__ == "__main__":
    main()
