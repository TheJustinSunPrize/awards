#!/usr/bin/env python3
"""Exact-arithmetic checks for the supplied k=1000 witness.

This is an independent numerical check, NOT a Lean kernel certificate and
NOT a verification of the universally quantified theorem in JSP001007.lean.
The 2.5-billion-point surviving set is checked through its exact interval
endpoints, rather than by sampling its elements.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any


class VerificationError(ValueError):
    """The proposed finite witness failed a required check."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def is_prime(n: int) -> bool:
    """Deterministic trial division; no probabilistic primality tests."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def integer(data: dict[str, Any], key: str) -> int:
    value = data.get(key)
    require(type(value) is int, f"{key} must be an integer")
    return value


def verify(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    data = json.loads(raw)
    require(isinstance(data, dict), "The witness must be a JSON object")
    q = integer(data, "q")
    # The artifact is deliberately one concrete finite witness, not a generic
    # prime-enumeration service accepting arbitrarily large untrusted inputs.
    require(q == 10_000, "This verifier is for the supplied q=10000 witness")
    M, J, H = q * q, q // 100, 2 * q + 1
    T, N = M // 4, J * M
    for name, value in {"M": M, "J": J, "H": H, "T": T, "N": N}.items():
        require(integer(data, name) == value, f"Inconsistent {name}")

    primes = data.get("primes")
    require(isinstance(primes, list), "primes must be a list")
    require(len(primes) == 1000, "Exactly 1000 primes are required")
    require(all(type(p) is int for p in primes), "Non-integer prime entry")
    require(all(a < b for a, b in zip(primes, primes[1:])),
            "The primes must be strictly increasing")
    require(all(M <= p < (q + 1) ** 2 for p in primes),
            "A modulus lies outside the prescribed square interval")
    require(all(is_prime(p) for p in primes), "A modulus is not prime")
    require(all(p > 2 and p % 2 == 1 for p in primes),
            "All moduli must be odd primes")
    all_block_primes = [p for p in range(M, (q + 1) ** 2) if is_prime(p)]
    require(integer(data, "prime_count_in_block") == len(all_block_primes),
            "Incorrect count of primes in the full square interval")
    require(primes == all_block_primes[:1000],
            "This artifact specifies the first 1000 primes in the block")
    require(primes[-1] ** 10 < N ** 9, "The strict prime cutoff fails")
    require(M >= 64 and 8 * H <= M and 8 * J * H <= M,
            "The general window lemma's hypotheses fail")
    require(J > 0 and T > 0, "The surviving rectangle must be nonempty")
    require(4 * T <= M, "The residue windows could overlap adjacent blocks")

    # x = j*M + 3*T + s and x - j*p = 3*T+s-j*(p-M).
    # Because p>=M, its minimum is attained at j=J-1, s=0;
    # its maximum is attained at j=0, s=T-1. Both endpoints
    # are checked for EACH selected prime; there is no random sampling.
    margins: list[int] = []
    for p in primes:
        half = p // 2
        require(half == (p - 1) // 2, f"Wrong forbidden cardinality for {p}")
        minimum_residue = 3 * T - (J - 1) * (p - M)
        maximum_residue = 4 * T - 1
        require(half <= minimum_residue, f"A point hits a removed class mod {p}")
        require(maximum_residue < p, f"A window has the wrong quotient mod {p}")
        require(0 <= minimum_residue, f"Negative proposed residue mod {p}")
        margins.append(minimum_residue - half)
    first_point = 3 * T
    last_point = (J - 1) * M + 4 * T - 1
    require(1 <= first_point <= last_point <= N, "Survivors escape [1,N]")
    # Digits 3*T+s lie in [0,M), so the pairs (j,s) give distinct integers.
    subset_card = J * T
    require(integer(data, "certified_subset_cardinality") == subset_card,
            "Incorrect cardinality of the proposed surviving subset")
    require(10 * subset_card > N, "The required density contradiction fails")

    return {
        "status": "PASS: exact-arithmetic finite-witness checks",
        "lean_kernel_status": "NOT_RUN: this program does not invoke Lean",
        "universal_theorem_status": "NOT_VERIFIED_BY_THIS_PROGRAM",
        "witness_sha256": hashlib.sha256(raw).hexdigest(),
        "primality_method": "deterministic trial division through floor(sqrt(p))",
        "q": q,
        "number_of_selected_primes": len(primes),
        "number_of_primes_in_full_block": len(all_block_primes),
        "smallest_selected_prime": primes[0],
        "largest_selected_prime": primes[-1],
        "N": N,
        "surviving_subset_cardinality": subset_card,
        "surviving_subset_density": "1/4",
        "strict_density_margin_10_card_minus_N": 10 * subset_card - N,
        "strict_cutoff_margin_N9_minus_pmax10": str(N ** 9 - primes[-1] ** 10),
        "minimum_residue_margin_above_removed_half": min(margins),
        "first_surviving_subset_point": first_point,
        "last_surviving_subset_point": last_point,
        "quantifier_scope": "one specific k=1000 witness only",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", nargs="?", type=Path,
                        default=Path(__file__).with_name("finite_witness_1000.json"))
    parser.add_argument("--output", type=Path,
                        help="Also write the actually obtained verification report")
    args = parser.parse_args()
    try:
        report = verify(args.witness)
    except (OSError, ValueError, TypeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    rendered = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    print(rendered, end="")
    if args.output is not None:
        args.output.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
