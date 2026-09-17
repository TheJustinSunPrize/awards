"""Check a concrete new-range prime tuple by exact trial division.

This supporting computation is separate from the universal Lean proof.
It does not enumerate the binomial-gcd minimum and does not establish an
infinite family. Only Python's integer arithmetic and standard library are used.
"""
import json
from math import isqrt
from pathlib import Path


def prime_by_trial_division(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d != 0 for d in range(3, isqrt(n) + 1, 2))


def main() -> None:
    p, a, b, c = 320001821, 2, 6, 20
    primes = [p, p + a, p + b, p + c]
    assert a >= 1 and b >= 3 * a
    assert c >= 3 * b + 1
    assert c < b * (b - a) + b + 1
    assert p >= 100 * c ** 5
    assert c < 10 * b ** 2
    assert all(prime_by_trial_division(n) for n in primes)
    result = {
        "P": p, "a": a, "b": b, "c": c,
        "primes": primes,
        "new_c_threshold": 3 * b + 1,
        "v2_c_threshold": b * (b - a) + b + 1,
        "old_c_threshold": 10 * b ** 2,
        "P_threshold": 100 * c ** 5,
        "satisfies_linear_hypotheses": True,
        "violates_v2_c_hypothesis": True,
        "violates_original_c_hypothesis": True,
        "primality_method": "Exact trial division by 2 and every odd integer through isqrt(n).",
        "trial_division_limits": [isqrt(n) for n in primes],
        "scope": "Supporting computation, separate from Lean. No direct enumeration of f(N), no infinitude claim."
    }
    path = Path(__file__).resolve().parent.parent / "verification" / "witness.json"
    path.parent.mkdir(exist_ok=True)
    path.write_bytes((json.dumps(result, indent=2) + "\n").encode("utf-8"))
    print("Exact trial division confirms a prime tuple in the newly admitted range.")


if __name__ == "__main__":
    main()
