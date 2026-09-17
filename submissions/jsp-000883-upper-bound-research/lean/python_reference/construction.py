"""Exact finite experiments for the proposed Erdős 1063 construction.

This module does not establish a universal theorem or check a Lean proof.
All arithmetic is integer arithmetic; Python >= 3.10, standard library only.
License: Apache-2.0. Prepared with ChatGPT assistance in this conversation.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
from math import comb, isqrt, lcm


def is_prime(n: int) -> bool:
    if not isinstance(n, int) or isinstance(n, bool):
        raise TypeError("n must be an integer")
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d != 0 for d in range(3, isqrt(n) + 1, 2))


def admissible_primes(k: int) -> list[int]:
    """Primes p with k < 2p and 3p + 2 <= 2k (no floating point)."""
    if not isinstance(k, int) or isinstance(k, bool) or k < 2:
        raise ValueError("k must be an integer >= 2")
    return [p for p in range(k // 2 + 1, (2 * k - 2) // 3 + 1) if is_prime(p)]


def lcm_initial(k: int) -> int:
    if not isinstance(k, int) or isinstance(k, bool) or k < 2:
        raise ValueError("k must be an integer >= 2")
    value = 1
    for j in range(1, k):
        value = lcm(value, j)
    return value


def valuation(n: int, p: int) -> int:
    """v_p(n), with the domain checked explicitly."""
    if n <= 0 or not is_prime(p):
        raise ValueError("valuation requires n > 0 and prime p")
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


@dataclass(frozen=True)
class Construction:
    k: int
    p: int
    L: int
    m: int
    residue: int
    cutoff: int
    n: int
    direction: str
    exception_offset: int
    exception_prime: int


def construct(k: int, p: int) -> Construction:
    if not isinstance(k, int) or isinstance(k, bool) or k < 9:
        raise ValueError("finite construction is stated for k >= 9")
    if not is_prime(p) or not (k < 2 * p and 3 * p + 2 <= 2 * k):
        raise ValueError("p must be prime and satisfy k < 2p and 3p+2 <= 2k")
    L = lcm_initial(k)
    if L % p:
        raise ArithmeticError("p does not divide L")
    m = k * (L // p)
    residue = m % p
    cutoff = k - p - 1
    left = residue <= cutoff
    q = next(q for q in range(2, k + 1) if k % q == 0 and is_prime(q))
    return Construction(k, p, L, m, residue, cutoff,
                        m if left else m + k - 1,
                        "left" if left else "right", 0 if left else k - 1, q)


def bad_offsets(n: int, k: int) -> list[int]:
    if k < 2 or n < 2 * k:
        raise ValueError("requires k >= 2 and n >= 2k")
    c = comb(n, k)
    return [i for i in range(k) if c % (n - i) != 0]


def check_construction(t: Construction) -> dict:
    """Check ALL k divisibilities directly, independent of valuation reasoning."""
    k, p, n = t.k, t.p, t.n
    c = comb(n, k)
    bad = [i for i in range(k) if c % (n - i) != 0]
    multiples = [i for i in range(k) if (n - i) % p == 0]
    q = t.exception_prime
    a = max(valuation(j, q) for j in range(1, k))
    checks = {
        "n_ge_two_k": n >= 2 * k,
        "positive_interval": n - k + 1 > 0,
        "m_not_divisible_by_p": t.m % p != 0,
        "at_least_two_p_multiples": len(multiples) >= 2,
        "exactly_claimed_exception": bad == [t.exception_offset],
        "exception_is_m": n - t.exception_offset == t.m,
        "bound_n_le_three_L": n <= 3 * t.L,
        "exception_valuation_matches": valuation(c, q) == a,
        "exception_valuation_strict": valuation(c, q) < valuation(t.m, q),
    }
    row = asdict(t)
    row.update({"bad_offsets": bad, "p_multiple_offsets": multiples,
                "binomial_bit_length": c.bit_length(), "checks": checks,
                "passed": all(checks.values())})
    # Decimal strings keep large integers exact in JSON/JavaScript readers.
    for key in ("L", "m", "n"):
        row[key] = str(row[key])
    return row
