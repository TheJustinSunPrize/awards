# JSP-000301: the smallest consecutive powerful nonsquares

This is a self-contained Lean proof of the counterexample recorded in
[JSP-000301](../../problems/catalog-0301-0400.md#JSP-000301), together with a
kernel-checked proof that **12167 is the least positive starting value** of such
a pair. It imports only the standard library bundled with Lean 4.19.0.

The counterexample is already known:

- 12167 = 23^3.
- 12168 = 2^3 * 3^2 * 13^2.
- Both are strictly between 110^2 = 12100 and 111^2 = 12321.

The additional result here is an exhaustive formal exclusion of every starting
value from 1 through 12166. This is a formal verification contribution, not a
claim of a new mathematical discovery or priority over earlier formalizations.

## Scope and prior submissions

The catalog already states the negative answer. Related submissions include
[PR #13](https://github.com/TheJustinSunPrize/awards/pull/13),
[PR #17](https://github.com/TheJustinSunPrize/awards/pull/17),
[PR #33](https://github.com/TheJustinSunPrize/awards/pull/33), and
[PR #55](https://github.com/TheJustinSunPrize/awards/pull/55).
This package adds an explicit smallest-counterexample theorem and a reproducible
certificate check. It does not address the separate counting question in
[Erdos problem #365](https://www.erdosproblems.com/365).

This directory is proposed evidence for maintainer review. It does not create a
candidate or award record, assert independent review, or change the catalog's
eligibility and verification flags. Its placement can be adjusted by maintainers.
The proof and verification script were prepared with OpenAI Codex assistance.

## Formal statement and definitions

All declarations are in namespace `JSP000301` in [Proof.lean](Proof.lean).

- `Prime p`: p is at least two and has no divisor d with 2 <= d < p.
  The implementation uses a finite list; `prime_iff` proves the equivalence to
  this ordinary statement using natural-number divisibility.
- `Powerful n`: n is positive and every prime p dividing n satisfies p*p | n.
  This is the usual powerful-number definition, including 1.
- `Square n`: there exists a natural k with k*k = n.
- `Candidate n`: n and n+1 are powerful and neither is a square.
- `negative_answer`: the catalog's universal assertion is false.
- `smallest_counterexample`: `Candidate 12167` and every `Candidate n` satisfies
  `12167 <= n`. There is no hidden upper bound on n in this final statement.

`powerful_of_finite` justifies the finite divisor checks: every divisor of a
positive n is at most n. `not_square_between` rules out square roots on either
side of 110 and 111 without a bounded square definition.

## Minimality certificate

For every n from 1 to 12166, a natural w encodes one of four witnesses. Let
k = w / 4 and t = w % 4:

| t | Required fact | Consequence |
| --- | --- | --- |
| 0 | k*k = n | n is a square |
| 1 | k*k = n+1 | n+1 is a square |
| 2 | k is prime, k divides n, k*k does not divide n | n is not powerful |
| 3 | k is prime, k divides n+1, k*k does not divide n+1 | n+1 is not powerful |

`certificate_sound` proves that each witness excludes `Candidate n`.
`check_sound` proves that successful sequential checking excludes every index in
that list's interval. There are 121 blocks of 100 entries and a last block of 66.
Each `verifiedN` is checked by `decide +kernel`; `minimality` covers all intervals.
The blocks limit memory use during kernel reduction. The witness data is not an
assumption: Lean verifies primality, divisibility, squares, and full coverage.

## Reproduce

Install the official [Lean 4.19.0 toolchain](https://github.com/leanprover/lean4/releases/tag/v4.19.0).
With Python 3.10 or newer and that `lean` executable on PATH, run from the
repository root:

```sh
python submissions/jsp-000301-minimality/verify.py
```

Alternatively pass `--lean /path/to/lean`. No Python packages, Mathlib, network
access, or native compilation are required by the verification script.
The `lean-toolchain` file also selects this release when using elan inside this
directory. To check only the formal proof from this directory:

```sh
lean -s 262144 Proof.lean
```

The stack argument is in KiB. The Python script separately regenerates all
witnesses using integer square roots and trial division, checks the first pair,
then runs Lean with a ten-minute timeout. The Python arithmetic is a cross-check;
the formal conclusions depend on Lean's kernel, not on Python output.

The three printed axiom audits contain only `propext` and `Quot.sound`.
There are no admitted statements, custom axioms, native-decision axioms, or unsafe
proof shortcuts. See [verification.txt](verification.txt) for the local run and
source hash. This is an author-side verification record, not an independent
review or a repository CI proof check. The existing CI checks repository records;
it does not execute this Lean file.

Code and documentation follow the repository's existing licensing terms.
