"""Exact independent arithmetic cross-check; the Lean kernel checks the proof.

Mathematical data: Han Wang, arXiv:2605.21518v1, Sections 9-11.
This Python script is not imported or trusted by the Lean proof.
"""
from fractions import Fraction
from math import gcd, isqrt, prod

PRIMES9 = (2, 3, 11, 17, 101, 157, 1979, 10093, 16879)
N9 = 5998279018951962402
P10 = 5998279018951962403
N10 = 35979351189199316534587473905773572006


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    for p in PRIMES9:
        require(p >= 2 and all(p % d for d in range(2, isqrt(p) + 1)),
                f"Small factor is not prime: {p}")
    require(prod(PRIMES9) == N9 == P10 - 1, "Factorization of P10 - 1")
    require(pow(3, P10 - 1, P10) == 1, "Fermat congruence")
    print("P10 primality certificate, base 3; q, residue, gcd(residue-1, P10):")
    for q in PRIMES9:
        residue = pow(3, (P10 - 1) // q, P10)
        divisor = gcd(residue - 1, P10)
        require(divisor == 1, f"Certificate failed for q={q}")
        print(q, residue, divisor)
    for n, primes, count in ((N9, PRIMES9, 9), (N10, (*PRIMES9, P10), 10)):
        require(len(primes) == len(set(primes)) == count, "Distinct factor count")
        require(prod(primes) == n, "Complete factorization")
        require(1 + sum(n // p for p in primes) == n, "Integer reciprocal identity")
        require(sum((Fraction(1, p) for p in primes), Fraction()) ==
                1 - Fraction(1, n), "Original rational equation")
        print(f"PASS: {n}, {count} distinct prime factors, exact reciprocal identity")
    require(N10 == N9 * P10, "Inheritance product")


if __name__ == "__main__":
    main()
