# JSP-000262: Wang's examples and general inheritance criteria

## English

This submission formalizes two explicit primary pseudoperfect numbers from
[Han Wang, *Port Fillings for Primary Pseudoperfect Numbers*, arXiv:2605.21518v1,
18 May 2026](https://arxiv.org/abs/2605.21518v1), Sections 9-11.
The mathematical results belong to that author. The contribution proposed here
is the Lean formalization and reproducible verification of these finite examples
and the general inheritance criteria in Section 5.

**This does not solve the infinitude question in
[Erdős Problem 313](https://www.erdosproblems.com/313).** It is a scoped partial-result
formalization submitted for intake, attribution and eligibility review. No
original mathematical discovery, priority, award tier, entitlement, official
verification or recipient confirmation is asserted.

## Exact result and statement correspondence

Let

```text
N9 = 5998279018951962402
P10 = N9 + 1 = 5998279018951962403
N10 = N9 * P10 = 35979351189199316534587473905773572006
```

The nine prime factors of `N9` are
`2, 3, 11, 17, 101, 157, 1979, 10093, 16879`.
The ten prime factors of `N10` are those nine together with `P10`.

[WangExamples.lean](WangExamples.lean) proves:

- Each listed factor is prime, including the 19-digit `P10`.
- Each list is the **entire** `Nat.primeFactors` finset of the corresponding number.
- Both numbers are squarefree, at least 2, and have exactly 9 and 10 distinct
  prime factors respectively.
- In the rational numbers, `1/n + sum (p in n.primeFactors) (1/p) = 1`.

[Audit.lean](Audit.lean) restates the two results with the literal integers,
Mathlib's `Nat.primeFactors`, `Nat.Prime`, and `Squarefree`, and the original
subtraction form `sum (p in n.primeFactors) (1/p) = 1 - 1/n`. A finset supplies
distinctness; it can be ordered increasingly to match the source's notation.
Thus no truncated divisor list, floating-point equality or empty witness is used.

The catalog summary omits the original problem's infinitude quantifier. These
finite witnesses must not be interpreted as closing that original problem.
The problem's completion, Lean and eligibility fields are left to the maintainers.

## Proof method

[Inheritance.lean](Inheritance.lean) additionally proves a general necessary and
sufficient condition for multiplying **any** primary pseudoperfect number `K`
by **any** natural number `C`. The product is primary pseudoperfect exactly when
`C` is positive and squarefree, coprime to `K`, and
`1/C + K * sum (p in C.primeFactors) (1/p) = 1`.
This includes the structural conditions in the equivalence rather than assuming
them without checking. The case `C = 1` is included; `C = 0` is excluded by the
proved positivity requirement.

The same file proves the one-prime criterion `q = K + 1`, the two-prime criterion
`(p - K) * (q - K) = K^2 + 1`, and the addition rule for the number of distinct
prime factors under coprime extension. The two-prime statement requires distinct
new primes, and subtraction there is in the integers. Mathematical attribution
for these criteria remains with the cited source and its antecedents; their
formalization does not establish an infinite supply of extensions.

Small-prime certificates and exact integer/rational calculations are checked with
`norm_num`. The large prime uses Mathlib's `lucas_primality`, base 3, and the
complete prime factorization of `P10 - 1 = N9`. Modular exponentiation is proved
with `reduce_mod_char`; the residues are proved unequal to 1 using kernel `decide`.
The factor-product identities then give complete prime-factor sets and
squarefreeness. The final rational equalities are exact computations.

There is no `sorry`, `admit`, `native_decide`, custom axiom, external oracle or
assumed primality in the submitted Lean source. The printed dependencies of the
audited statements are `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

Use the pinned [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json):

- Lean `4.34.0`, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`).
- Python 3.10 or later; the arithmetic cross-check needs only the standard library.

In this directory, after installing the Lean toolchain:

```sh
lake exe cache get Mathlib/NumberTheory/LucasPrimality.lean Mathlib/Data/Nat/Squarefree.lean Mathlib/Tactic/NormNum/Prime.lean Mathlib/Tactic/ReduceModChar.lean Mathlib/Tactic/FieldSimp.lean Mathlib/Tactic/Ring.lean Mathlib/Tactic/Linarith.lean
python verify.py
```

The cache command downloads dependencies. `verify.py` builds the proof and audit,
re-elaborates all three source files, invokes `leanchecker`, and runs the independent
exact-arithmetic Python cross-check. It writes `verification-local.txt`, which is
ignored by Git. Inspect local output before publishing it.

See [verification.txt](verification.txt) for the reviewed local execution log and
[artifacts.json](artifacts.json) for file hashes and byte counts. These are local
verification evidence, not a designated verifier's attestation. `leanchecker`
replays declarations through Lean's own kernel; it is **not an independently
implemented proof checker**. Designated isolated verification, independent-checker
review and any required permanent external evidence archive remain pending.

Repository validation on Windows with `PYTHONUTF8=1`: `validate`, `build` and
`check` pass. The full 22-test validator suite has 20 passes, one failure
(`test_published_statement_immutable_and_superseded`) and one error
(`test_revocation_keeps_original_evidence`). The identical two failures were
reproduced against the unmodified upstream commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`; they involve Windows path separators
in history lookups. No validator or test code is changed by this submission.

## Attribution, related work and submission status

Mathematical attribution: Han Wang, arXiv:2605.21518v1, Theorems 9.1, 10.1 and 11.1,
Lemma 5.1 and Corollaries 5.2-5.3 (including the earlier work discussed there).
The paper has a CC BY 4.0 license. Its text and proof scripts are not copied here;
the mathematical data and base-3 certificate are attributed above. The Lean and
Python files in this package were prepared with OpenAI Codex assistance.

Proposed formalizer: `RECIPIENT-JSP-000262-A`, pending identity and contribution
confirmation. This is a self-submission on behalf of the submitting participant;
that interest is disclosed. No nomination for the mathematical solver's role is
made on the submitter's behalf.

[Related PR #545](https://github.com/TheJustinSunPrize/awards/pull/545) formalizes
the general denominator/product and uniqueness properties of Erdős 313 solutions.
This package instead verifies the two explicit 2026 examples, their prime-factor
counts, and general inheritance criteria. It neither imports nor copies that PR.
A search of public issue/PR titles
and bodies on 17 September 2026 found #545 and no matching submission for these
two examples; this bounded search is not proof of first formalization worldwide.

This package creates no candidate or award record and records no payout details.
Acceptance of this contribution and any award eligibility require organizer review.
Source code follows the repository's [MIT license](../../LICENSE); documentation
follows its [CC BY 4.0 content license](../../LICENSE-CONTENT).
