"""Tests for computation and failure detection, not Lean proof tests."""
import sys
import unittest
from dataclasses import replace
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from construction import (admissible_primes, bad_offsets, check_construction,
                          construct, is_prime, lcm_initial, valuation)


class ExactConstructionTests(unittest.TestCase):
    def test_primes(self):
        self.assertEqual([x for x in range(30) if is_prime(x)], [2, 3, 5, 7, 11, 13, 17, 19, 23, 29])

    def test_primes_no_float_boundary(self):
        self.assertFalse(is_prime(101 * 101))
        self.assertTrue(is_prime(101))

    def test_bad_prime_type(self):
        with self.assertRaises(TypeError):
            is_prime(7.0)

    def test_lcm(self):
        self.assertEqual(lcm_initial(9), 840)

    def test_first_case(self):
        t = construct(9, 5)
        self.assertEqual((t.m, t.n, t.direction), (1512, 1512, "left"))
        self.assertEqual(bad_offsets(t.n, t.k), [0])

    def test_right_direction(self):
        t = construct(22, 13)
        self.assertEqual(t.direction, "right")
        self.assertEqual(bad_offsets(t.n, t.k), [21])
        self.assertEqual(t.n - 21, t.m)

    def test_left_direction(self):
        self.assertEqual(construct(20, 11).direction, "left")

    def test_missing_prime_is_not_success(self):
        self.assertEqual(admissible_primes(10), [])

    def test_invalid_small_k(self):
        with self.assertRaises(ValueError):
            construct(8, 5)

    def test_invalid_composite_p(self):
        with self.assertRaises(ValueError):
            construct(16, 9)

    def test_invalid_lower_endpoint(self):
        with self.assertRaises(ValueError):
            construct(20, 7)

    def test_invalid_upper_endpoint(self):
        with self.assertRaises(ValueError):
            construct(20, 13)

    def test_bad_integer_range(self):
        with self.assertRaises(ValueError):
            bad_offsets(5, 3)

    def test_valuation(self):
        self.assertEqual(valuation(72, 2), 3)
        self.assertEqual(valuation(72, 3), 2)
        self.assertEqual(valuation(72, 5), 0)

    def test_bad_valuation(self):
        for n, p in [(0, 2), (-2, 2), (20, 4)]:
            with self.assertRaises(ValueError):
                valuation(n, p)

    def test_detect_wrong_exception_offset(self):
        t = replace(construct(9, 5), exception_offset=1)
        self.assertFalse(check_construction(t)["passed"])

    def test_detect_wrong_n(self):
        t = replace(construct(9, 5), n=1513)
        self.assertFalse(check_construction(t)["passed"])

    def test_finite_range_all_primes(self):
        count = 0
        for k in range(9, 101):
            for p in admissible_primes(k):
                with self.subTest(k=k, p=p):
                    t = construct(k, p)
                    self.assertTrue(check_construction(t)["passed"])
                    # Independently read the interval from low endpoint to high.
                    bad = [d for d in range(t.n - k + 1, t.n + 1) if comb(t.n, k) % d]
                    self.assertEqual(bad, [t.m])
                count += 1
        self.assertGreater(count, 0)


if __name__ == "__main__":
    unittest.main()
