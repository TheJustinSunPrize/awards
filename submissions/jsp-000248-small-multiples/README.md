# JSP-000248: a uniform small-multiple obstruction

**Partial Progress — new formalization of an elementary obstruction.** For
every positive integer `m`, prime `p` and positive exponent `k`, this package
proves

```text
m * m! < p  →  m * p^k cannot be the largest denominator
               in a representation of 1 by distinct positive unit fractions.
```

The principal declaration is
`JSP248.small_multiple_prime_power_not_largestDenominator` in
[`SmallMultipleObstruction.lean`](SmallMultipleObstruction.lean).
[`Audit.lean`](Audit.lean) expands every condition on the denominator set and
gives the infinite family `2 * 5^(k+1)` as a consequence. The bound is sufficient,
and no optimality of `m * m!` is asserted.

## Exact statement and proof

`JSP248.IsLargestDenominator n` means that a finite set `S : Finset ℕ` is
contained in `[1,n]`, contains `n`, and satisfies
`∑ d ∈ S, (1 : ℚ) / d = 1`. A finite set gives distinct denominators; membership
of `n` makes the maximum attained. Denominator 1 is allowed, and the supporting
file proves that `{1}` is a valid representation. All parameters in the main
theorem are universally quantified, with hypotheses exactly
`0 < m`, `p.Prime`, `m * m.factorial < p`, and `0 < k`.

Write `q=p^k`. Split the denominator set into the multiples of `q` and the
remaining terms, then multiply its reciprocal sum by `m! * q`. A multiple
`d=q*j` has `1≤j≤m`, so its scaled term is the integer `m!/j`. The distinct
quotients give at most `m` terms. This part is therefore a positive integer
`A≤m*m!<p`, since the maximum denominator itself occurs. Every remaining
scaled term has p-adic norm less than one. If the original sum were one,
the complete scaled sum would also have norm less than one. The
nonarchimedean inequality would imply `p | A`, contradicting `0<A<p`.

The supporting prime-power file proves the unique-largest-valuation
obstruction, its nonintegrality conclusion, the prime-power special case,
and infinitude of exceptions. These are support for the principal
small-multiple extension; priority for the prime-power result is not claimed.

## Scope and attribution

The mathematical prime-power and small-multiple observations are attributed to
Erdős and Graham by Greg Martin, [*Denser Egyptian fractions*, arXiv:math/9811112v1,
Introduction, pages 3–4](https://arxiv.org/pdf/math/9811112), published in
*Acta Arithmetica* 95 (2000), 231–260. The explicit factorial cutoff here is an
elementary sufficient condition formalized by the argument above. This is not
a claim of a new mathematical discovery.

The complete JSP248 question concerns which integers occur as largest
denominators. **This package does not classify all such integers, prove the
density-one theorem, or formalize Martin's sharp exceptional-count asymptotic.**
It supplies an unconditional infinite obstruction family, including composite
numbers beyond prime powers, as partial formalization progress.

Existing work is preserved and distinguished:

- [plby/lean-proofs E292 at commit 8822f7d…](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos292.lean)
  proves density one. Its source credits Greg Martin and formal authors
  Codex / GPT-5.6 Sol. Its definition unfolds to the same rational finite sum,
  but none of its proof code is imported or copied here.
- [PR93](https://github.com/TheJustinSunPrize/awards/pull/93), inspected at
  `e3f5144b41c0c41fbc9783d0dcdf54d28045a7bd`, supplies finite certificates.
- [PR114](https://github.com/TheJustinSunPrize/awards/pull/114), inspected at
  `a308b3de8a4cce8eeea492023c52b207b753716e`, **already contains a complete
  prime-power obstruction formalization**, despite its held-review description.
  This prior implementation is acknowledged; the claimed extension here is
  the uniformly quantified small-multiple theorem. Its proof code was not copied.
- Mathlib supplies p-adic norms, valuations and finite-sum infrastructure,
  retaining its own authorship and Apache-2.0 license.

The dated source comparison and exact paths are recorded in
[`PRIOR-WORK.md`](PRIOR-WORK.md).

The submitting account is `zifanersuotang`; Codex assisted development,
review and verification. Proposed formalizer identity remains
`RECIPIENT-JSP000248-SMALLMULTIPLES-A` pending confirmation. This is a
self-submission with an interest in review, not an independent referee
attestation. No award, acceptance, eligibility or payment is asserted.

## Reproduce

The project pins Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, including inherited revisions in
`lake-manifest.json`. With the pinned toolchain installed:

```sh
lake exe cache get
python verify.py
```

Alternatively, pass `--mathlib /path/to/pinned/mathlib` and
`--lean-root /path/to/lean-4.33.0` to use an existing dependency checkout.
The verifier rebuilds these three local modules into a fresh `build/<run_id>/`
and explicitly runs `leanchecker` on each. It binds the replayed objects to
that run's compilation and requires all 11 selected axiom reports. Each run
keeps its logs and summary in `verification/runs/<run_id>/`;
`verification/summary.json` records the latest status, including any failure.

Imported Mathlib and standard-library artifacts are trusted. The bundled
checker uses the same Lean kernel implementation; no independent checker
implementation or clean rebuild of all dependencies is claimed. Contributor
verification does not replace the project's required official review.

The source is Apache-2.0 licensed; see [LICENSE](LICENSE). Historical
mathematical facts are cited, and no third-party proof body is redistributed.

## Recorded verification

The contributor run on 2026-09-16T23:32:54.236665+00:00 completed all three
compilations and all three explicit `leanchecker` replays successfully. All 11
audited declarations report only subsets of `propext`, `Classical.choice`,
and `Quot.sound`; no additional axioms were reported. See
[`verification/summary.json`](verification/summary.json) for exact source, tool,
object and log hashes, timings, and the expanded-statement audit output.
The run used the pinned existing dependency checkout described above.
The `lake exe cache get` bootstrap command and a separate `lake build` were
not executed in this contributor run.

[`ARTIFACTS.json`](ARTIFACTS.json) gives SHA-256 and byte counts for every
published package file except the manifest itself. Logs preserve merged tool
output with known local paths redacted; summaries also record the hashes and
byte counts of the captured original output. Git commit pinning is the public
artifact identifier; no independently administered archival service is claimed.
