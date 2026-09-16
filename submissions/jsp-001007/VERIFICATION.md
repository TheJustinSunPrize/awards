# JSP-001007 — verification record (prepared by the formalizing contributor)

Contributor evidence, not a curator verification record.

## 1. Environment (pinned)

| Item | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc1` (`lean-toolchain`) |
| Mathlib revision | `96f4f6ca6e9dcdb26fec36ec10fa90c7f424e94d` (`lakefile.toml`) |
| Package | `jsp-001007`, library `Jsp`, six modules |
| Build command | `./verify.sh` |

## 2. Reproduction result

`evidence/build.log` records `lake build` succeeding and the axiom audit printing

```text
'JSP001007.counterexample_core'   depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001007.primeCount_lower'      depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001007.clustering'            depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001007.green44_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001007.not_green44_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `native_decide`, no extra `axiom`s.  The placeholder scan over `Jsp/*.lean`
and `Jsp.lean` is empty.

## 3. Statement correspondence

| Source statement | Formal counterpart |
| --- | --- |
| Green's problem 44: `2 ≤ p₁ < ⋯ < p₁₀₀₀ < N^(9/10)`, remove half the classes mod `pᵢ`, is the survivor set `≤ N/10`? | refuted for every `k` by `green44_counterexample` with `p i ^ 10 < N ^ 9` |
| Erdős #1202: `k` primes `< n^(1-ε)`, `Aᵢ` of size `(pᵢ-1)/2` | `(A i).card = (p i - 1) / 2`, `p i ^ 10 < N ^ 9` (i.e. `p i < N^(9/10)`, the `ε = 1/10` case) |
| "the surviving set has size `> N/10`" | `N / 10 < (survivors N p A).card` |

The formal statement is the `ε = 1/10` quantitative form; since the conjecture asks for a
single `k` that works for all configurations, exhibiting a counterexample for **every** `k`
(as `green44_counterexample` does) refutes it.

## 4. Scope and limitations

* The construction follows the public write-up of Price and GPT-5.4 Pro; the prime-count
  input, clustering and numerical assembly are independent formalizations.
* Only the counterexample direction is formalized (not the large-sieve positive result for
  primes below `N^(1/2)`).
* The final threshold `N₀` is expressed using `10^20` and the existence thresholds from
  the clustering and logarithm lemmas; no small numerical bound or optimized threshold is claimed.
* No curator, verifier or third party has reviewed this package; no award level, recipient
  status or payment entitlement is claimed.

## 5. Direct conclusion and independent verification

`JSP001007.not_green44_conjecture` explicitly refutes the recorded one-parameter
conjecture at `ε = 1/10`. It handles `k = 0` and proves the required conversions
from natural-number division to a real density bound and from tenth powers to
the real exponent `9/10`.

The final counterexample and its dependency closure have also been checked with
nanoda 0.4.17, a separate type checker implemented in Rust. The final submission
records the completed check of both endpoints in `evidence/nanoda.log` and exact
versions and export hashes in `evidence/metadata.json`. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted by the checker configuration.
The submitter ran these automated checks; independent human statement review
remains pending.
