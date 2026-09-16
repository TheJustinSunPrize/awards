# JSP-000865 / Erdős 1042: zero-diameter semantic review

Review date: 2026-09-16. Reviewer: the separate AI subagent `/root/official_review` within the same Codex task. This is an additional AI source review, **not** a human signature, organizer-appointed verification, independent proof-checker run, or award attestation. No compilation was requested or performed in this review, and no Lean source was changed.

## Result and limits

**No mathematical statement-fidelity defect was identified in the new eventual component-gap theorem.** The positive comparison level works at diameter zero, and the downstream argument needs no positive lower bound on the diameter. The conclusion is substantive for nonempty sets; it does not rely on an empty-domain loophole or on counting an infinite component type as zero.

The precise incremental contribution is the removal of `0 < d` from the **general compact/closed-set, eventual component-gap branch** of the existing formalization. It is not a first formalization of Erdős 1042. The upstream connected-set branch with `d ≤ 1/4` already includes connected sets of diameter zero; the new result removes the connectedness restriction for the zero boundary of the gap assertion.

Two qualifications must remain visible in a submission:

1. The proportional gap holds for **all sufficiently large degrees**, uniformly over root configurations in the fixed set. It is not an all-degrees assertion. A degree-one monic polynomial has one component, so `1 ≤ (1-c)` would fail for every `c > 0`.
2. The cited Ghosh–Ramachandran paper explicitly works with positive capacity in its notation and Theorem 2.1(a). The zero-boundary result is an extension of the existing argument. Do not describe the published theorem as already explicitly quantified over capacity zero, or claim a new mathematical discovery or worldwide formalization priority from this review.

## Reviewed versions

| File | SHA-256 of reviewed local bytes |
| --- | --- |
| `proof/JSP000865/Upstream.lean` | `10fb91b2f8e43418adb8bde402e7f1d15d769c5267a72aa813bf42b000e47817` |
| `plby/src/latest/ErdosProblems/Erdos1042.lean` | `10fb91b2f8e43418adb8bde402e7f1d15d769c5267a72aa813bf42b000e47817` |
| `proof/JSP000865/ZeroCapacity.lean` | `bdf4b880193392f537899087560cbd31ca29585a41aa5b452f8158aee93382ef` |

The copied upstream file is byte-for-byte identical to the isolated plby source at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The project toolchain file specifies Lean `v4.33.0`; the checked local Mathlib checkout is `db584cd6d46c92f209a44c0f1c829460d327499d`. These observations identify sources, not a successful build.

The new uniform-gap proof, from `obtain ⟨ε, hε, hprod⟩ :=` through its final contradiction, was compared with the upstream proof after the same point and is textually identical after trimming surrounding whitespace. The substantive alteration is the preceding Fekete-witness lemma and the removal of the positivity premise.

During the review, the parent agent appended `erdos_1042_including_zero` and its axiom-print command. The resulting version was read again and is the final hash listed above. That combined theorem reuses the upstream capacity-one witness and connected small-diameter clause, and substitutes the new all-subunit gap clause. Its statement and conjunction assembly introduce no additional mathematical change. The earlier reviewed file hash was `1fba7bfc398fdfb9cb07d985cee9b89bd006e894335a8a6be974a459defc5d12`.

## Mathematical target

The new theorem `closed_subunit_transfiniteDiameter_hasUniformComponentGap` at line 103 states:

```text
IsClosed K → HasTransfiniteDiameter K d → d < 1 →
  ∃ c > 0, ∃ N, ∀ n ≥ N, ∀ z : Fin n → ℂ,
    (∀ i, z i ∈ K) →
    componentCount (rootPolynomial z) ≤ (1-c) n.
```

`zero_transfiniteDiameter_hasUniformComponentGap`, line 96, specializes to `d = 0`. The intermediate compact-set theorem is at line 38. The constant and cutoff are selected before `n` and the root tuple, so they are uniform over all sufficiently large degrees and all root configurations in the same fixed `K`. They can depend on `K`; the result does not promise a bound determined only by the numerical diameter.

The original question's Fekete formula and strict sublevel set are recorded in the cached [Erdős 1042 page](https://www.erdosproblems.com/1042). The cited [Ghosh–Ramachandran paper](https://arxiv.org/html/2312.13673v1) defines its asymptotic component ratio in the introduction and frames Question 1.2 using that ratio. Its section 1.1 assumes positive capacity and Theorem 2.1(a) establishes the subunit case under that convention. Thus the eventual quantifier in the Lean statement is appropriate; extending to zero is the added boundary result.

## Definition review

### Fekete diameter and boundedness

`Upstream.lean:48–67` defines the mutual-distance product over `i < j`, so each unordered pair appears once. For `n ≥ 2`, the exponent is `1 / choose(n,2)`, matching the displayed problem formula. Values for `n = 0,1` are set to zero and do not affect the limit at infinity. Tuples may have repeated points; their product is zero, which is legitimate in the supremum and does not exclude or distort distinct-point configurations.

`feketeDiameter K n` is the real supremum of these values over tuples in `K`. `HasTransfiniteDiameter K d` is the conjunction of boundedness of `K` and convergence of those suprema to the real value `d`. It assumes the Fekete limit; it does not substitute an unrelated invariant or assume the component conclusion. The proof need not establish existence of the limit for every compact set because the problem and target supply the diameter as a hypothesis.

The boundedness conjunct is significant: an unbounded collection has no finite real supremum in the intended extended-real sense, while Lean's total real `sSup` has a default for unbounded inputs. Requiring boundedness avoids treating that default as a finite geometric diameter. The theorem concerns finite Fekete transfinite diameter. The phrase “arbitrary closed sets” in the zero-theorem comment is therefore read together with `HasTransfiniteDiameter`, not as an assertion about all unbounded closed sets or all possible extensions of potential-theoretic capacity.

For a nonempty bounded `K`, the tuple-value set is nonempty and bounded above by `bddAbove_feketeValues`; `feketeValue_le_feketeDiameter` uses that upper bound correctly. For the empty set, `Real.sSup_empty = 0` is the Mathlib convention (confirmed in `Mathlib/Algebra/Order/Archimedean/Real/Basic.lean:171`). This gives the conventional zero diameter. There is no positive-degree root tuple contained in the empty set, so its component-gap conclusion is harmlessly vacuous. The main theorem does not rely on the set being empty.

No equality between this Fekete definition and a separate potential-theoretic capacity definition is proved in the reviewed files. The formal statement uses the explicit transfinite-diameter definition in the question. Any explanatory use of “capacity” should retain that convention for compact sets.

### Polynomial, multiplicity, and degree

`rootPolynomial` at line 481 is exactly `∏ i, (X - C (z i))`, the monic polynomial specified in the question. It makes no injectivity assumption on `z`, so repeated roots and their multiplicities are included. The accompanying monicity and `natDegree = n` lemmas at lines 495 and 498 rule out cancellation or a hidden reduction from degree to the number of distinct roots.

At `n = 0` the product is `1`, whose strict unit lemniscate is empty. At positive degree it is a nonconstant monic polynomial. These boundary cases are compatible with the eventual statement. No division by `n` occurs in the new proof without a positive-degree hypothesis: its counterexample sequence satisfies `n k ≥ k+1`.

### Connected components and the `Nat.card` issue

`unitLemniscate p` is `{w | ‖p.eval w‖ < 1}` (line 485), retaining the **strict** inequality. This matters: touching boundary components can merge if the set is changed to a closed sublevel set.

`componentCount` is `Nat.card (ConnectedComponents (unitLemniscate p))` (line 489). Although `Nat.card` evaluates to zero for an infinite type, that convention does not trivialize the target here. For every positive-degree `rootPolynomial z`, the upstream proof establishes `indexedRootComponent_surjective` at line 1365: the finite root-index type `Fin n` maps onto the connected-component type. Consequently that type is finite and its natural cardinality is the actual number of components.

The surjectivity proof uses `component_contains_root` at line 1333. That argument applies the maximum-modulus principle to the inverse polynomial on a purported root-free component, using boundedness and the boundary modulus bound to obtain a contradiction. Thus every nonempty component contains a root. This supports the finite count with the intended analytic reasoning, rather than an assumed finite cardinality.

Repeated roots do not invalidate the later counting estimate. `componentCount_le_sub_card_add_one` at line 1423 collapses a nonempty set of **indices** whose roots lie in a common connected region to one representative, and maps the remaining indices onto the other components. Multiple equal roots already map to the same component. The estimate can overcount remaining indices, which is safe for an upper bound.

### Uniformity and closed-to-compact conversion

`HasUniformComponentGap` at lines 1599–1602 spells out the positive constant, degree cutoff, and universal tuple quantifiers. It neither requires the conclusion only along a chosen subsequence nor allows a new constant for each polynomial. The new closed-set corollaries obtain compactness from closedness and the boundedness inside `HasTransfiniteDiameter`, using the finite-dimensional complex-plane Heine–Borel property.

## Review of the new comparison level

Set `a = max d 0` and `q = (a+1)/2`. From `d < 1` we obtain `0 ≤ a < 1` and `d ≤ a`. Therefore

```text
0 < q < 1,       d ≤ a < q.
```

At `d = 0`, this is simply `q = 1/2`. The code derives the same strict inequalities with `max_lt` and linear arithmetic. Convergence of the Fekete diameters to `d` then gives `feketeDiameter K m < q` eventually; intersection with `m ≥ 2` supplies a usable finite Fekete witness. The positive comparison parameter is distinct from the possibly zero diameter.

The original downstream regularization lemma requires `q > 0`, `q < 1`, and this finite witness; it does not require `d > 0`. Compactness turns the strict product bound at regularization zero into a common positive regularization parameter. The later empirical-measure and component-count argument depends only on that regularized product bound.

The contradiction establishing uniformity is also mathematically consistent. If no uniform gap exists, the code chooses degrees `n k ≥ k+1` and configurations whose ratios exceed `1-1/(k+1)`. A weakly convergent empirical-measure subsequence yields a fixed positive loss `c`; eventually `1/(φ k+1) < c`, contradicting the selected configurations. The positive degree factors ensure that multiplying the coefficient inequalities preserves strictness. There is no remaining appeal to `d > 0` or to a finite list of degrees.

Actual Fekete diameters are nonnegative, so a negative `d` cannot be the limit under these definitions. The new lemma does not need that auxiliary fact: its comparison argument is valid for every real `d < 1`. In particular, it does not derive the zero case by assuming an impossible negative diameter.

## Non-vacuity and edge cases

Take the nonempty compact set `K = {a}`. Every Fekete product with at least two nodes is zero, so `HasTransfiniteDiameter K 0` is satisfied mathematically. For every positive `n`, the only root configuration gives `(X-C a)^n`, whose strict unit lemniscate is the open unit disk centered at `a`, with one component. The asserted gap is concretely satisfied by `c = 1/2` and `N = 2`. This gives a nonempty, arbitrarily-large-degree test of both the assumptions and conclusion; it was reasoned through here, not added as a compiled example.

More generally, a nonempty finite set with `r` distinct points has zero Fekete diameter and at most `r` components for any positive-degree root polynomial, because each component contains a distinct root value. This includes disconnected zero-diameter sets, which are outside the upstream connected-set branch. These observations confirm that the new quantifiers address actual configurations with repeated roots and growing degree.

An empty `K` has no positive-degree configurations, and the regularization lemma handles its empty tuple space explicitly. Negative degrees are impossible because degrees are natural numbers. Small positive degrees are deliberately outside the eventual guarantee when necessary. No edge case found makes the substantive nonempty claim vacuous.

## Validation not performed and acceptable claim wording

The reviewed two files have no lexical `sorry`, `admit`, custom `axiom`/`constant` declaration, `native_decide`, or `unsafe` occurrence. This is a source check, not a proof that the compiled target depends only on approved axioms. The `#print axioms` commands at the bottom of `ZeroCapacity.lean` have not been executed by this reviewer. Successful compilation, actual target axiom reports, fresh reproduction, and any operator-required checker review remain separate evidence.

A faithful contribution description is: “Incremental Lean extension of the existing Erdős 1042 formalization, removing the positive-diameter hypothesis from the eventual component-gap assertion and explicitly including zero transfinite diameter for closed bounded sets.” It should credit Ghosh–Ramachandran for the mathematical foundation and the pinned plby formalization for the reused definitions and argument. This review supports that limited semantic claim; it does not establish priority, recipient eligibility, independent verification completion, or an award.
