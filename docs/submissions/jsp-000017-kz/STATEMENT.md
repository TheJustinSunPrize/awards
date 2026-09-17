# Statement fidelity and requested review

Official record: [JSP-000017, pinned catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000017).

The original question quantifies over every number of runners, every set of
distinct constant real speeds, and every chosen reference runner. All runners
start at one point of a unit-circumference circle. A qualifying time gives
distance at least the reciprocal of the total runner count to every other
runner.

| Requirement | Formal statement |
| --- | --- |
| Unit circle and its circular distance | Mathlib `UnitAddCircle` and `dist`; no replacement by ordinary real-line distance |
| Common starting point | Position at time t is the class of `t * speed r` |
| Arbitrary signed real speeds | `speed : Fin 3 ↪ ℝ` or `speed : Fin (m+2) ↪ ℝ` |
| Distinct speeds | `Function.Embedding` injectivity |
| Time | One `t : ℝ` with `0 < t`; implies the usual `0 <= t` |
| All competitors at that time | Universal quantifier over `s != r` inside the same existential time |
| Unrestricted three-runner case | `three_runners` and `three_runners_spec`; threshold `1/3` |
| Known doubling family | `doubling_runners`; threshold `1/((m:ℝ)+2)` |
| Explicit additional family condition | A list covering all competitors has consecutive absolute relative speeds satisfying `2*abs(v_i-v_r) <= abs(v_{i+1}-v_r)` |
| General conjecture | Not proved; higher counts with unrestricted relative speeds remain outside this submission |

The file's `Safe` predicate is an auxiliary real interval description. The
lemma `norm_ge_of_safe` proves its consequence in the actual quotient-circle
norm, and `relative_distance` proves the passage from relative velocity to
distance between actual moving runners. The final declarations use the circle
metric itself.

The list assumptions in `doubling_runners` include both exclusion of the
reference runner and coverage of every other runner. No competitor is silently
discarded. The underlying `doubling_band` uses only finitely many velocity
positivity and ratio assumptions; it proves a common nonempty interval, with
the final interval allowed to have zero length. Closed inequalities and a
strictly positive time survive this limiting endpoint case.

This is a formalization of known results, not a proposed new mathematical
solution. The catalog still marks the full problem ineligible. Please assess
whether the scoped formalization is substantive and eligible for contribution
recognition, as well as overlap, provenance, statement fidelity and intake
placement. No candidate or award status is created by this package.

Proposed contributor: `RECIPIENT-JSP-000017-KZ-A`, confirmation pending.
AI assistance: OpenAI ChatGPT/Codex. Mathematical attribution is given in
README.md; no global priority or sole manual authorship is claimed.
