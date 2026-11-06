import csv
import io
import json
import tempfile
import unittest
from contextlib import redirect_stdout
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from flint import arb, ctx

import prove_erdos as verifier
import verify_central_mpfr as mpfr
from repair_admissibility import exact_rational_score

ROOT = Path(__file__).resolve().parent.parent


def certificate(kind, param=None, multiplier="0.3"):
    return {"lo": "-0.1", "hi": "0.1", "active": [
        {"kind": kind, "param": param, "lambda": multiplier, "B": "-999"}
    ]}


class ArbVerifierTests(unittest.TestCase):
    def setUp(self):
        self.precision = ctx.prec
        self.decimal_precision = getcontext().prec
        ctx.prec = 160
        getcontext().prec = 80

    def tearDown(self):
        ctx.prec = self.precision
        getcontext().prec = self.decimal_precision

    def test_derivatives_and_antiderivatives_agree(self):
        cases = [("t", None), ("-t", None), ("t2", None), ("-t2", None),
                 ("t4", None), ("-t4", None), ("cos", "1.3"), ("-cos", "1.3"),
                 ("sin", "1.3"), ("-sin", "1.3"), ("cos+asin", ["1.3", "-0.4"]),
                 ("harmonic_cos", "3"), ("weighted_parseval", {"weights": {"1": "0.2", "3": "0.7"}}),
                 ("parseval_combined", {"lambda_W": "0.4", "coefficients": {"1": "0.4", "3": "-0.2"}})]
        for kind, param in cases:
            with self.subTest(kind=kind):
                terms, floats, _, _ = verifier.prepare_bin(certificate(kind, param), arb("1e-14"))
                x, h = arb("0.37"), arb("1e-12")
                derivatives = verifier.q_derivs(terms, x)
                self.assertAlmostEqual(float(derivatives[0]), verifier.q_float(floats, 0.37), places=12)
                difference = (verifier.Q(terms, x + h) - verifier.Q(terms, x - h)) / (2 * h)
                self.assertAlmostEqual(float(difference), float(derivatives[0]), places=12)
                for order in range(1, 4):
                    difference = (verifier.q_derivs(terms, x + h)[order - 1]
                                  - verifier.q_derivs(terms, x - h)[order - 1]) / (2 * h)
                    self.assertAlmostEqual(float(difference), float(derivatives[order]), places=10)

    def test_sine_positive_part_integral(self):
        with mp.workdps(70):
            constant = 1 + 20 * mp.sin(2)
            left = mp.asin(constant / 20)
            right = mp.pi - left
            primitive = lambda x: constant * x + 20 * mp.cos(x)
            expected = primitive(left) - primitive(-2) + primitive(2) - primitive(right)
        upper, _ = verifier.upper_integral_bin(certificate("sin", "1", "20"),
            Decimal("0.00001"), 0.0001, 1001, 100000, arb(0))
        self.assertGreaterEqual(float(upper.upper()) + 1e-12, float(expected))
        self.assertLess(float(upper.upper()) - float(expected), 1e-7)

    def test_second_moment_bin_crossing_zero(self):
        self.assertTrue(verifier.rhs_expected("-t2", None, "-0.1", "0.2").overlaps(-arb(2) / 3))

    def test_negative_fourth_moment_uses_cauchy_schwarz(self):
        self.assertTrue(verifier.rhs_expected("-t4", None, "0", "0.1").overlaps(-arb(4) / 9))

    def test_stored_rhs_is_not_trusted(self):
        item = certificate("t", multiplier="1")
        terms, _, _, _ = verifier.prepare_bin(item, arb(0))
        self.assertTrue(terms[0].B >= arb("0.1"))

    def test_invalid_constraints_are_rejected(self):
        invalid = [("unknown", None, "1"), ("cos", "0", "1"), ("t", None, "-1"),
                   ("t", None, "NaN"), ("sin", "Infinity", "1"),
                   ("harmonic_cos", "0", "1"), ("harmonic_cos", "1.2", "1"),
                   ("weighted_parseval", {"weights": {"1": "1.0000000000000001"}}, "1"),
                   ("weighted_parseval", [["1", "0.6"], ["1", "0.6"]], "1"),
                   ("parseval_combined", {"lambda_W": "-1", "coefficients": {"1": "-2"}}, "1"),
                   ("parseval_combined", {"lambda_W": "0.1", "coefficients": {"1": "0.1000000000000001"}}, "1"),
                   ("parseval_combined", {"coefficients": {"1": "0.1"}}, "1")]
        for kind, param, multiplier in invalid:
            with self.subTest(kind=kind, param=param):
                with self.assertRaises(ValueError):
                    verifier.prepare_bin(certificate(kind, param, multiplier), arb(0))

    def test_negative_inflation_is_rejected(self):
        with self.assertRaises(ValueError):
            verifier.prepare_bin(certificate("t"), arb("-1e-14"))

    def test_empty_or_reversed_cover_is_rejected(self):
        for bins in ([], [{"lo": "1", "hi": "-1"}], [{"lo": "-1", "hi": "-0.1"}, {"lo": "0.1", "hi": "1"}]):
            with self.assertRaises(ValueError):
                verifier.repair_tiny_bin_gaps({"bins": bins})

    def test_tiny_gap_is_closed_by_enlargement(self):
        data = {"bins": [{"lo": "-1", "hi": "0"}, {"lo": "1e-16", "hi": "1"}]}
        self.assertEqual(verifier.repair_tiny_bin_gaps(data), 1)
        self.assertEqual(data["bins"][1]["lo"], "0")

    def test_empty_duplicate_or_out_of_range_selection_is_rejected(self):
        for text in ("", ",", "1,1", "3", "2-1", "-1"):
            with self.assertRaises(ValueError):
                verifier.parse_bins(text, 3)

    def test_partial_run_cannot_claim_complete_proof(self):
        data = {"bins": [{"lo": "-1", "hi": "0", "active": []}, {"lo": "0", "hi": "1", "active": []}]}
        with redirect_stdout(io.StringIO()):
            result = verifier.verify(data, "0.2", [0], "0.001", 0.001, 0, 100, "0", 4, None)
        self.assertTrue(result["proved_all_checked_bins"])
        self.assertFalse(result["proved_all_bins"])

    def test_parallel_and_serial_bounds_agree(self):
        data = {"bins": [{"lo": "-1", "hi": "0", "active": []}, {"lo": "0", "hi": "1", "active": []}]}
        with redirect_stdout(io.StringIO()):
            serial = verifier.verify(data, "0.2", [0, 1], "0.001", 0.001, 0, 100, "0", 4, None)
            parallel = verifier.verify(data, "0.2", [0, 1], "0.001", 0.001, 0, 100, "0", 4, None, jobs=2)
        self.assertEqual(serial["worst_D_upper_ball"], parallel["worst_D_upper_ball"])
        self.assertTrue(parallel["proved_all_bins"])

    def test_shipped_certificate_is_admissible(self):
        data = json.loads((ROOT / "certs/erdos_elevated_candidate.json").read_text(), parse_float=str, parse_int=str)
        verifier.repair_tiny_bin_gaps(data)
        self.assertEqual(len(data["bins"]), 178)
        for item in data["bins"]:
            verifier.prepare_bin(item, arb("1e-14"))


class MpfrInputTests(unittest.TestCase):
    def test_shipped_inputs(self):
        mpfr.validate_coefficients(mpfr.COEFFS)
        with mpfr.MANIFEST.open(newline="") as stream:
            self.assertEqual(len(mpfr.validate_chunks(csv.DictReader(stream))), 32)

    def test_non_grid_endpoint_is_rejected(self):
        with self.assertRaises(ValueError):
            mpfr.units("0.00001")

    def test_incomplete_or_overlapping_partition_is_rejected(self):
        for rows in ([], [{"lo": "0", "hi": "1"}], [{"lo": "0", "hi": "1.1"}, {"lo": "1", "hi": "2"}]):
            with self.assertRaises(ValueError):
                mpfr.validate_chunks(rows)

    def test_invalid_coefficient_files_are_rejected(self):
        original = mpfr.COEFFS.read_text()
        mutations = [original.replace("T2 0.8838047458203124", "T2 -0.8838047458203124"),
                     original + "PI 1 0\n", original.replace("WINDOW 0.00043990552724552023", "WINDOW 0"),
                     original.replace("COS 5.94", "COS 0"), original.replace("COS 5.94", "COS NaN")]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "coefficients.txt"
            for content in mutations:
                path.write_text(content)
                with self.assertRaises(ValueError):
                    mpfr.validate_coefficients(path)

    def test_decimal_rounding_is_outward(self):
        value = Fraction(1, 3)
        self.assertLessEqual(Fraction(mpfr.floor_places(value, 15)), value)
        self.assertGreaterEqual(Fraction(mpfr.ceil_places(value, 15)), value)


class ExactIdentityTests(unittest.TestCase):
    def test_profile_compression_preserves_all_lag_maximum(self):
        for values, denominator in (([1, 1, 3, 3], 4), ([0, 0, 4, 4], 4), ([1, 2, 3, 4], 5), ([1] * 12, 2)):
            n = len(values)
            exact = max(Fraction(2, n) * sum((Fraction(values[i], denominator) * (1 - Fraction(values[i + m], denominator))
                        for i in range(max(0, -m), min(n, n - m))), Fraction(0)) for m in range(-(n - 1), n))
            score, lag = exact_rational_score(values, denominator)
            self.assertEqual(score, exact)
            self.assertTrue(-(n - 1) <= lag <= n - 1)

    def test_fourth_moment_cancellation(self):
        for f1, f2, f3, f4 in ((Fraction(1, 7), Fraction(2, 9), Fraction(-1, 11), Fraction(1, 13)), (0, Fraction(1, 3), 0, Fraction(1, 5))):
            expanded = (Fraction(2, 5) - f4) + 4 * f3 * f1 + 6 * (Fraction(2, 3) - f2) * f2 + 4 * f1 * f3 + f4
            self.assertEqual(expanded, Fraction(2, 5) + 4 * f2 - 6 * f2**2 + 8 * f1 * f3)

    def test_line_bundle_square_completion(self):
        s, u, v, alpha = map(Fraction, ("0.2", "-0.4", "0.7", "-2"))
        difference = (1 + alpha**2) * s**2 - (2 * s * u - u**2 - v**2 + 2 * alpha * s * v)
        self.assertEqual(difference, (u - s)**2 + (v - alpha * s)**2)
        self.assertGreaterEqual(difference, 0)


if __name__ == "__main__":
    unittest.main()
