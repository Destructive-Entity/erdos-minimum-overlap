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
│   └── paper.tex                  # Full LaTeX source
├── formal/
│   └── Erdos36.lean               # Lean 4 formalization
├── certs/
│   ├── erdos_elevated_candidate.json         # 178-bin dual certificate
│   ├── ultra_dense_8192_best.json            # n = 8192 step-function profile
│   └── verified_elevated_arb_report.json     # Report of a full Arb run
└── scripts/
    ├── prove_erdos.py             # 160-bit Arb interval ball verifier
    ├── verify_quadrisected_mpfr.c # 192-bit MPFR order-6 Taylor verifier source
    ├── verify_central_mpfr.py     # Compiles and runs the MPFR verifier on 32 chunks
    ├── certify_leaders.py         # Exact evaluation of the step-function profile
    ├── repair_admissibility.py    # Admissibility checker for rational profiles
    ├── weighted_038056070_center_manifest.csv
    └── weighted_center_combined_038056070.txt
```

## Replication

Requirements: Python 3.9 or later with `python-flint`, `mpmath`, `numpy` and `scipy`; a C compiler with the GNU MPFR and GMP libraries; for the Lean file, Lean 4 with Mathlib.

```bash
pip install python-flint mpmath numpy scipy
```

### Arb verification of the certificate

```bash
python3 scripts/prove_erdos.py certs/erdos_elevated_candidate.json --order 4 --prec 160 --target 0.38056171
```

Certifies all 178 bins against the target $0.38056171$ and reports the worst bin, $[-1/512, 0]$, with $D \le 2.62769470$. The run takes about eight minutes on two cores.

### MPFR cross-check of the central window

```bash
python3 scripts/verify_central_mpfr.py
```

Compiles `scripts/verify_quadrisected_mpfr.c`, evaluates the 32 chunks listed in `scripts/weighted_038056070_center_manifest.csv` and reports $D \le 2.62769373$.

### Exact evaluation of the step-function profile

```bash
python3 scripts/certify_leaders.py certs/ultra_dense_8192_best.json
```

The evaluation is in exact rational arithmetic and is slow at resolution 8192.

### Lean 4 file

From a Lake project that depends on Mathlib:

```bash
lake env lean formal/Erdos36.lean
```

## Citation

```bibtex
@article{xing2026erdos36,
  title={Certified Lower Bounds and Variational Dynamics for the Erd{\H{o}}s Minimum Overlap Problem},
  author={Xing, Jayden},
  journal={arXiv preprint},
  year={2026}
}
```

## License
MIT License. See [LICENSE](LICENSE) for details.
