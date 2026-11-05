# Erdős Problem 36: Certified Bounds for the Minimum Overlap Problem

[![Lean 4](https://img.shields.io/badge/Lean_4-Mathlib-blue)](formal/Erdos36.lean)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

This repository contains the publication manuscript, certified verification engines, dual certificates, and Lean 4 formalization for **Erdős Problem #36** (the Minimum Overlap Problem).

---

## Results Summary

* **Certified Lower Bound**:
  $$\mu > 0.38056239 \qquad (D_{\max} \le 2.62769001)$$
  Certified across all 178 bins covering $[-1, 1]$ via 160-bit Arb interval ball arithmetic (`scripts/prove_erdos.py`), with the critical central subdivision ($m = 1/5120$) verified via 192-bit MPFR directed interval arithmetic with order-6 Taylor remainder bounding (`scripts/verify_mpfr_quadrisected`).

* **Constructive Upper Bound**:
  $$\mu \le 0.38085905681456...$$
  Certified exact rational admissible-outright partition on $n = 8192$ with zero box violations (`certs/ultra_dense_8192_best.json`).

* **Machine-Checked Formal Proofs**:
  Foundational algebraic inequalities, fourth-moment balance identities, and majorant duality reductions formalized in Lean 4 with zero `sorry` against Mathlib (`formal/Erdos36.lean`).

---

## Repository Structure

```
.
├── paper/
│   ├── paper.pdf                  # Publication manuscript
│   └── paper.tex                  # Full LaTeX source
├── formal/
│   └── Erdos36.lean               # Lean 4 formalization
├── certs/
│   ├── erdos_elevated_candidate.json         # 178-bin certified dual certificate
│   ├── ultra_dense_8192_best.json            # n=8192 exact rational certificate
│   ├── exact_transcendental_mu_100digits.json # 100-digit analytical evaluation
│   └── verified_elevated_arb_report.json     # Arb verification report
└── scripts/
    ├── prove_erdos.py             # 160-bit Arb interval ball verifier
    ├── verify_quadrisected_mpfr.c # 192-bit MPFR order-6 Taylor verifier source
    ├── verify_mpfr_quadrisected   # Compiled MPFR binary
    ├── verify_quadrisected_world_record.py # Driver for 32 central chunks
    ├── certify_leaders.py         # Exact rational certificate verifier
    ├── repair_admissibility.py    # Admissibility checker for rational profiles
    ├── verify_exact_transcendental_mu.py # 100-digit analytical evaluator
    ├── weighted_038056070_center_manifest.csv
    └── weighted_center_combined_038056070.txt
```

---

## Replication Instructions

### Prerequisites
- Python 3.9+ with `flint` (`python-flint`), `mpmath`, `numpy`
- GCC / Clang with `libmpfr` and `libgmp`
- (Optional) Lean 4 (version 4.35.0+)

```bash
pip install python-flint mpmath numpy
```

### 1. Verify Central Bisection (192-bit MPFR Engine)
The critical central subdivision ($m = 1/5120$) is certified across all 32 chunks via the high-order MPFR verifier:

```bash
python3 scripts/verify_quadrisected_world_record.py
```

To recompile the C verifier from source:
```bash
gcc -O3 scripts/verify_quadrisected_mpfr.c -lmpfr -lgmp -o scripts/verify_mpfr_quadrisected
```

### 2. Verify Full-Domain Dual Certificate (160-bit Arb Ball Engine)
Verifies all 178 bins in `certs/erdos_elevated_candidate.json` across 131,691 interval nodes:

```bash
python3 scripts/prove_erdos.py certs/erdos_elevated_candidate.json --order 4 --prec 160
```

### 3. Verify Exact Rational Upper Bound Profile
Verifies that the $n=8192$ partition is admissible outright with zero box violations:

```bash
python3 scripts/certify_leaders.py certs/ultra_dense_8192_best.json
```

### 4. Evaluate 100-Digit Analytical Closed Form
Evaluates the variational Jacobi elliptic equioscillation closed-form solution to 100 decimal digits:

```bash
python3 scripts/verify_exact_transcendental_mu.py
```

### 5. Check Lean 4 Formalization
To check the machine-verified formal proofs in `formal/Erdos36.lean`:

```bash
lake env lean formal/Erdos36.lean
```

---

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
