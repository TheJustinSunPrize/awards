# JSP-000733: Korsky's constant-error upper bound for primitive subset sums

This package formalizes Samuel Korsky's upper bound for **Erdős Problem 882**.
Let `F(n)` be the maximum size of a subset of `{1,...,n}` whose distinct nonempty
subset-sum values never divide one another. For every natural number `n`, the
final theorem proves

```text
F(n) ≤ Nat.log 2 n + 1.
```

For `n ≥ 1`, `Nat.log 2 n` is `floor(log₂ n)`. At zero the natural-logarithm
convention is `Nat.log 2 0 = 0`; the extremal definition gives `F(0)=0`.

The mathematical source is **Samuel Korsky**, *Near-Exact Bounds for Primitive
Subset Sums* (July 26, 2026), Proposition 2.2, equation (2.6), equivalently the
sum inequality (1.6) in Theorem 1.1. The upper-bound consequence appears as
inequality (3.6) in the proof of Corollary 1.2. The
[author's manuscript](https://drive.google.com/file/d/1G1kNGljoP7qn32niEu87fCWcGKjQvWk4/view)
was linked in the [proof-claims thread](https://www.erdosproblems.com/forum/thread/882/proof-claims).
That listing is not a certification by the website's moderators. See
[ATTRIBUTION.md](ATTRIBUTION.md) for the author's disclosed AI assistance and
related formal work.

The proposed contribution is a Lean formalization of this bound using a finite
modular presentation of the ordered ternary packing argument, with a complete
bridge to the original finite extremal problem. **It is not a new mathematical
discovery or an exact formula for `F(n)`.** Lower bounds, a two-value theorem,
and the manuscript's further balanced-difference estimates are outside the
submitted formalization's scope.

## Exact exported statements

| Theorem in `Erdos882Korsky` | Scope |
|---|---|
| `korsky_sum_bound` | For `k > 0` and positive natural weights with no nonempty subset sum twice another, `k * 2^(k-1) ≤ Σ aᵢ`. |
| `original_upper_bound` | For every natural `n`, `Erdos882.maximumSize n ≤ Nat.log 2 n + 1`. |

The original extremal quantity is independently defined as the maximum of the
finite set of attainable admissible cardinalities, with a proved attainment
lemma. The final exported statements have no unproved packing, injectivity,
counting-bound, or maximum-attainment assumption. The intermediate proof
parameters are supplied by the final assembly.

## Proof structure

- `KorskyDefs.lean`: the no-double subset-sum condition and ordered ternary words.
- `KorskyCount.lean`: an explicit bijection and induction give the word count
  `k * 2^(k-1)` for every positive `k`.
- `KorskyInject.lean`: coefficient cancellation excludes equal weighted values
  and collisions differing by the total sum.
- `KorskyModular.lean`: weighted values inject into residue classes modulo their
  positive total. The constant-2 word, whose residue is zero, is included.
- `Erdos882Original.lean`: independent definitions of the original subset-sum
  condition and actual extremal maximum, with maximum attainment.
- `KorskyEndpoint.lean`: enumeration of an admissible set, the bridge from
  primitivity to the no-double condition, and the integer logarithm bound.
- `Erdos882Korsky.lean`: the two final theorem assemblies and axiom reports.

The [source-scope review](SCOPE_AUDIT.md) explains statement fidelity and boundary
cases. It is an automated source review, not a human signature or designated
organizer verification. [Third-party notices](THIRD_PARTY_NOTICES.md) distinguish
mathematical attribution from source-code reuse.

## Related submissions

[PR #31](https://github.com/TheJustinSunPrize/awards/pull/31) formalizes the leading
asymptotic and excludes the stronger additive-error results. The later
[PR #264](https://github.com/TheJustinSunPrize/awards/pull/264), reviewed at head
`1db509ec5ad2c410d9b13232685c343c008f0b1f`, formalizes, for `n ≥ 32`,

```text
F(n) ≤ log₂(n) + (1/2)log₂(log₂(n)) + 3.
```

Its original-condition and maximum-attainment bridges are proved. Those
contributions are acknowledged. The current constant additive-error endpoint
is a stronger statement. No proof source from either PR or from the separately
published lower-construction formalization is incorporated in this package.

The prior-work search is bounded. It does not establish globally first
formalization priority or an award entitlement. The mathematical strengthening
is credited to Korsky, and recognition of the formalization remains subject to
review.

## Reproduction

Use Lean **4.34.0**, Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`, and the transitive dependency pins in
`lake-manifest.json`. Check [source-manifest.json](source-manifest.json) before
running tools. Prepare dependency sources and caches before denying network
access.

```sh
lake exe cache get
lake build Erdos882Korsky
python3 tools/verify.py \
  --project . --module Erdos882Korsky \
  --theorem Erdos882Korsky.korsky_sum_bound \
  --theorem Erdos882Korsky.original_upper_bound \
  --lean-bin /path/to/lean-4.34.0/bin \
  --exporter /path/to/compatible/lean4export \
  --nanoda /path/to/nanoda_bin \
  --output verification/local-run --threads 1 --deny-network
```

The verifier compiles the local import closure serially, runs the matching
fresh Lean kernel checker, exports the two theorem closures, and runs Nanoda
with only the three standard allowed axioms. `--deny-network` uses macOS
`sandbox-exec`; users on other platforms must record their actual isolation
arrangements. Tool identities and run outcomes belong in the verification
receipt, not in an assertion inferred from these commands.

## Evidence and official review

[VERIFICATION.md](verification/VERIFICATION.md) records the actual verification
run, exit codes, source identities, checker results, and limitations. The local
workflow denies network access and tests that denial against an accessible
control. It does not claim filesystem isolation or a full rebuild of all
Mathlib dependencies; cached dependency objects are used.

The archive status, artifact identifiers, hashes, and byte counts must be read
from that evidence record. Neither a local ZIP nor an ordinary GitHub package
is represented here as permanent external archival. A reproducible export is
not, by itself, an archive receipt.

Under the [official rules](https://www.hejustinsun.com/prize/rules), Lean checking
is an entry prerequisite, followed by designated verification, PR finalization,
and award assessment. This package requests review of a formalization
contribution. It changes no recipient, award-allocation, signature, or payment
record. The rules distinguish mathematical solver and formalizer roles; any
formalizer allocation is conditional on an award and the organizer's confirmed
attribution, not a guaranteed payment.
