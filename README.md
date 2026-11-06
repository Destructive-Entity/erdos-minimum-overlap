# Erdős Problem 36: Certified Bounds for the Minimum Overlap Problem

[![Lean 4](https://img.shields.io/badge/Lean_4-Mathlib-blue)](formal/Erdos36.lean)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

This repository contains the manuscript, the verification programs, the dual certificates and the Lean 4 file for Erdős Problem #36 (the minimum overlap problem).

## Results

**Lower bound.** $\mu > 0.38056171$ ($D_{\max} \le 2.62769470$). The 178-bin dual certificate `certs/erdos_elevated_candidate.json` is verified on every bin in 160-bit Arb ball arithmetic by `scripts/prove_erdos.py`. As an independent cross-check, the 192-bit MPFR verifier `scripts/verify_quadrisected_mpfr.c` evaluates the central certificate of Deng with the second-moment bound of the window $|\bar{x}| \le 1/1280$ and gives $D \le 2.62769373$ on that window.

**Discretized profile.** `certs/ultra_dense_8192_best.json` describes a step function with 512 steps whose overlap norm, evaluated exactly, is $0.38085905681456\ldots$. It does not improve the known upper bounds.

**Lean 4.** `formal/Erdos36.lean` contains no `sorry`. The elementary algebraic steps are proved in Lean; the analytic inputs, the theorem of Swinnerton-Dyer and the numerical certificate are stated as axioms.

## Repository Structure

```
.
├── paper/
│   ├── paper.pdf                  # Publication manuscript
│   ├── paper.tex                  # Full LaTeX source
│   └── arxiv-source.zip           # Source-only submission archive
├── formal/
│   ├── Erdos36.lean               # Algebraic reductions and explicit axioms
│   ├── lean-toolchain             # Pinned Lean release
│   ├── lakefile.toml
│   └── lake-manifest.json          # Pinned Mathlib dependencies
├── certs/
│   ├── erdos_elevated_candidate.json         # 178-bin dual certificate
│   ├── ultra_dense_8192_best.json            # n = 8192 step-function profile
│   ├── verified_elevated_arb_report.json     # Aggregate Arb report
│   └── verified_elevated_arb_bins.csv        # Every certified bin
└── scripts/
    ├── prove_erdos.py             # 160-bit Arb interval ball verifier
    ├── test_verifiers.py          # Regression tests
    ├── verify_quadrisected_mpfr.c # 192-bit MPFR order-6 Taylor verifier source
    ├── verify_central_mpfr.py     # Compiles and runs the MPFR verifier on 32 chunks
    ├── certify_leaders.py         # Exact evaluation of the step-function profile
    ├── repair_admissibility.py    # Admissibility checker for rational profiles
    ├── weighted_038056070_center_manifest.csv
    └── weighted_center_combined_038056070.txt
```

## Replication

Requirements: Python 3.12 or later; a C compiler with the GNU MPFR and GMP development libraries; for the Lean file, the toolchain and Mathlib commit pinned in `formal/`. The Python checks were run with Python 3.13.17.

```bash
python3 -m pip install -r requirements-verification.txt
```

### Arb verification of the certificate

```bash
python3 scripts/prove_erdos.py certs/erdos_elevated_candidate.json --order 4 --prec 160 --target 0.38056171 --jobs 2
```

Certifies all 178 bins against the target $0.38056171$ and reports the worst bin, $[-1/512, 0]$, with $D \le 2.62769470$. The aggregate report records input SHA-256 hashes, and `certs/verified_elevated_arb_bins.csv` records the per-bin bounds. The verifier checks exact multiplier and harmonic coefficient inequalities before integration.

### MPFR cross-check of the central window

```bash
python3 scripts/verify_central_mpfr.py
```

Checks the coefficient signs, spectral inequalities and exact partition of `[0, 2]`, then compiles `scripts/verify_quadrisected_mpfr.c` and evaluates all 32 chunks. The result is $D \le 2.62769373$ on the stated central window, not a global bound by itself. The option `--mean-denominator` accepts `320`, `512`, `1280` and `5120` to reproduce the manuscript table.

### Exact evaluation of the step-function profile

```bash
python3 scripts/certify_leaders.py certs/ultra_dense_8192_best.json
```

The evaluator uses exact integer correlation and losslessly compresses equal consecutive blocks. For the supplied 8192 entries this reduces the computation to 512 steps without changing the represented function.

### Lean 4 file

The repository pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```bash
cd formal
lake update
lake exe cache get
lake build
```

The analytic and certificate axioms are not proved by this command. The integral axioms include integrability and boundedness hypotheses.

### Regression tests

```bash
python3 -m unittest discover -s scripts
ruff check --select F,E9 scripts
```

The tests cover derivative/antiderivative agreement, a sine positive-part integral, exact feasibility checks, invalid and incomplete certificates, MPFR partition coverage, and lossless profile compression.

### Manuscript build

```bash
cd paper
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex
```

`paper/arxiv-source.zip` contains only the self-contained LaTeX source, with the bibliography included. The PDF is not included in the source archive.

## Citation

```bibtex
@unpublished{xing2026erdos36,
  title={Certified Lower Bounds and Variational Dynamics for the Erd{\H{o}}s Minimum Overlap Problem},
  author={Xing, Jayden},
  note={Manuscript; source and verification programs available at the repository URL},
  url={https://github.com/Destructive-Entity/erdos-minimum-overlap},
  year={2026}
}
```

## License
Original contributions are under the MIT license. Upstream attribution and licensing scope are stated in [LICENSE](LICENSE).
