# Statement, prior work and claim boundary

The target is the leading asymptotic of the maximum cardinality, with the
same positive-integer domain, nonempty subset-sum **values**, primitivity
predicate and attained finite maximum as the retained lower-bound source.
It proves `maximumSize(n) / log₂(n) → 1`. It does not determine the exact
maximum, the published half-log-log error term, or a bounded additive error.

The [original problem page](https://www.erdosproblems.com/882) records the
ELRSS lower bound greater than `log₂(n)−1` and a sharper upper bound than
the elementary counting bound used here. Both suffice for the same leading
limit. Equal subset-sum values are allowed by primitivity; the new bridge
derives injectivity instead of assuming it. The empty sum is included in
the injection and counting step, and `n=0,1` do not affect the final limit.

## Checked prior formal sources

- [plby lower construction](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean)
  supplies the original definitions, attained maximum and lower bound. It
  is retained as an exact Git blob with its formal-author header. Its final
  theorem is a lower bound, rather than the leading limit.
- [lean-genius conditional counting](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos882ProblemOQ03.lean)
  includes genuine counting results assuming distinct subset sums. That
  work is acknowledged. The package here supplies the bridge from the
  actual primitive-values condition and uses the same maximum as the lower
  construction. The [associated main wrapper](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos882Problem.lean)
  assumes custom upper/lower-bound axioms; those are not dependencies of
  this package. Six related Lean files were inspected in that repository.
- Two [ryantuck statement files](https://github.com/ryantuck/erdos-ai/blob/f32b2886f8f005d481533036d0af4fe36e8e48f7/conjectures/882.lean)
  were located and read; their relevant lower/upper targets use `sorry`.
  Finding incomplete statement files does not establish global absence of
  a completed proof elsewhere.

This bounded search and direct source comparison support describing the
added files as a completion relative to the checked prior sources. They do
not prove global priority. The mathematical observation and counting
argument are established mathematics, and no mathematical discovery is
claimed.

## Stronger mathematical claim outside the target

The [proof-claims discussion](https://www.erdosproblems.com/forum/thread/882/proof-claims)
contains Samuel Korsky's 27 July 2026 claim, crediting GPT 5.6-Pro, of a
stronger finite bound and exact values for infinitely many inputs. Its
[linked mathematical PDF](https://drive.google.com/file/d/1G1kNGljoP7qn32niEu87fCWcGKjQvWk4/view)
was read during the review and contains no Lean proof or code link. The
host labels such claims as potentially unexamined; this package does not
referee or formalize that claim. It therefore makes no categorical claim
that a constant-error mathematical result is still unknown.

## Review and checking

Separate Codex subagents reviewed the finite bridge and the analytic
sandwich argument, with no mathematical gap found. These are source
reviews, not signatures from independent human prize reviewers. Actual
compiler and target-module replay results are only those recorded by the
completed verification script. No curator approval, two-checker official
record, recipient consent, or award eligibility follows from these checks.
