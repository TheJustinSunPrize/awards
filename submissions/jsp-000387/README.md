# JSP-000387: distinct partial sums for the full nonzero field

This package formalizes the full-field construction described in
[issue #46](https://github.com/TheJustinSunPrize/awards/issues/46).
The elementary mathematical argument is already recorded there. This package
contributes a Lean proof, not a claim of a new mathematical discovery.

## Submission and attribution

Prepared with OpenAI Codex assistance. This is a self-submitted formalization
for maintainer review, with the mathematical construction attributed to the
prior explanation in issue #46. No first-formalization or discovery-priority
claim is made.

The official [Selection Rules](https://www.hejustinsun.com/prize/rules),
sections 4.1 and 6, describe a Lean-containing PR and subsequent verification.
This repository's contribution guide primarily specifies public-record
maintenance. Following the proposed package layout used in
[PR #13](https://github.com/TheJustinSunPrize/awards/pull/13), `submissions/` is
a proposed intake location, not an established or approved submission route.
Maintainers are asked to confirm whether this supplementary full-field lemma
is in scope and redirect the package if a different location is required.

## Exact scope

Let `K` be any finite field and let `q` be its cardinality. There exists an
ordering `a(0), ..., a(q-2)` of all nonzero elements of `K` such that the sums

`S(m) = a(0) + ... + a(m-1)`, for `1 <= m <= q-1`,

are pairwise distinct. The zero-length sum `S(0)` is excluded. For `q > 2`,
the last sum is zero, so including `S(0)` would give a false statement.
The two-element field is included in the theorem.

The public declaration `JSP000387.exists_full_field_ordering` in
[FullField.lean](FullField.lean) assumes only `Field K` and `Fintype K`.
Its predicate `IsFullFieldOrdering` explicitly asserts:

1. Every entry with index less than `q-1` is nonzero.
2. These entries are pairwise distinct.
3. Every nonzero element occurs at one of these indices.
4. The nonempty prefix sums, including the last sum, are pairwise distinct.

The sequence is represented by a function on natural numbers; only its first
`q-1` entries constitute the ordering. Thus no fixed field size, finite test
range, or unproved generator assumption replaces the general statement.

## Proof

The multiplicative group `K*` is cyclic of order `q-1`. Choose a generator `g`
and set `a(j) = g^j` for `0 <= j < q-1`. Powers in this range enumerate `K*`
without repetition.

For every positive integer `m`, the telescoping identity gives

`S(m) * (g - 1) = g^m - 1`.

If `S(m) = S(n)`, multiply both sides by `g-1` and cancel the subtracted `1`
to obtain `g^m = g^n`. Since `g` is nonzero, cancelling one factor of `g`
gives `g^(m-1) = g^(n-1)`. The exponents `m-1` and `n-1` are both in
`{0, ..., q-2}`, where the powers are distinct, so `m = n`.

This argument never divides by `g-1`, and therefore also works when `q=2`
and `g=1`. The formal proof uses Mathlib's finite-domain cyclicity theorem,
geometric-sum identity, and injectivity of powers below the element order.

For example, in the field of five elements, the generator `2` yields
`[1, 2, 4, 3]` with nonempty prefix sums `[1, 3, 2, 0]`.

## Relation to the original problem

The [catalog entry](../../problems/catalog-0301-0400.md#JSP-000387) currently
uses the full-nonzero-field wording. However, the cited paper by Noah Kravitz,
[*Rearranging small sets for distinct partial sums*](https://arxiv.org/abs/2407.01835),
states the Graham--Erdos conjecture for **every subset** of the nonzero
elements of a prime field, and proves a small-subset result.

This package does not prove that arbitrary-subset conjecture. Restricting the
geometric ordering to a subset does not preserve the prefix-sum argument.
Issue #46 discusses restoring that stronger intended statement; related
[PR #47](https://github.com/TheJustinSunPrize/awards/pull/47) instead proposes
marking the literal full-set version solved. This package leaves that editorial
decision to the maintainers and can serve as supplementary formal evidence for
the full-set lemma in either case.

No candidate, recipient, eligibility, claim, or award record is asserted by this
package. Its local checks are not independent review. The finite-field result
and its proof are credited to the elementary construction recorded in issue
#46; the original arbitrary-subset conjecture and Kravitz's partial result
retain their separate scope and attribution.

## Reproduction

The package pins Lean `4.34.0` and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The Lake manifest pins transitive
dependencies. Install Lean with the standard Lean toolchain manager, then run
the following commands from this directory:

```sh
lake exe cache get Mathlib.RingTheory.IntegralDomain Mathlib.Algebra.GroupWithZero.Units.Fintype
bash verify.sh
```

The script builds the package, recompiles the proof with warnings treated as
errors, checks [Audit.lean](Audit.lean), and invokes
`lake env leanchecker --fresh --verbose FullField`. The guarded axiom checks
fail if the dependency list differs from `propext`, `Classical.choice`, and
`Quot.sound`, including if a placeholder proof adds `sorryAx`.

Mathlib's cache supplies dependency artifacts; the submitted proof is compiled
locally. Fresh replay rechecks the module and its imported constants from an
empty environment. The bundled `leanchecker` uses Lean's own kernel; it is not
an independently implemented proof checker. See [VERIFICATION.md](VERIFICATION.md)
for the recorded local run and [SHA256SUMS](SHA256SUMS) for the source hashes.
The sanitized [verification log](verification.log) records the submitted run.

The awards repository's ordinary validation does not compile Lean packages.
Run the commands here separately when reviewing this contribution.
