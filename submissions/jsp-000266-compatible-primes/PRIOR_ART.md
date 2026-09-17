# Attribution, related formal work and contribution boundary

## Mathematical source

Sandro Bettin, Loïc Grenié, Giuseppe Molteni and Carlo Sanna, [A lower bound for the number of Egyptian fractions, arXiv:2509.10030v1](https://arxiv.org/html/2509.10030v1), 12 September 2025. This fixed version supplies the definitions of U and compatible primes, Lemmas 1 and 2, and the compatible-prime extension in Lemma 4. Its eventual-prime argument motivates the finite numerator cutoff here. The mathematical extension is not attributed to this submitter.

We do not formalize the full Lemma 4 corollary using the explicit harmonic-lcm threshold, nor the paper's main analytic lower bound. Our finite maximum cutoff proves eventual compatibility but gives no efficient large-input algorithm.

The [official JSP-000266 record at the submission base](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#jsp-000266) describes the overall problem as solved, with Lean proof and eligibility both marked No. This package does not purport to supply the matching upper bound attributed there to other contributors. The catalog's “Lean proof: No” is not evidence that no related formal work exists.

## Existing Lean project

We inspected [joachimneu/distinct-reciprocal-subset-sums](https://github.com/joachimneu/distinct-reciprocal-subset-sums/tree/e51bf855d37c97cc66126b98144804c950f86872), pinned at `e51bf855d37c97cc66126b98144804c950f86872`, during this submission. It is substantial existing work, not an empty placeholder. We did not rebuild or independently audit that entire project.

In its [Doublings.lean](https://github.com/joachimneu/distinct-reciprocal-subset-sums/blob/e51bf855d37c97cc66126b98144804c950f86872/Erdos320/Lemmas/Doublings.lean#L280), `disjoint_of_modCheck` and `S_two_mul_of_modCheck` already prove a uniform modular criterion at `n=p^a*k`, with arbitrary exponent `a`, prime `p`, and `1≤k<p`. Its `SBasic.lean` also proves fundamental counting properties. The exact-doubling/cardinality bridge and prime-power phenomena should therefore not be described as first formalized here.

This package formalizes the BGMS **reduced-numerator compatibility** hypothesis for arbitrary positive seed `m`, without `m<p` or coprimality assumptions. It also connects that hypothesis to executable rational difference sets, a finite numerator cutoff, arbitrary-large compatible primes/multiples, and the lower bound counted by all irreducible indices. This is a precise statement-level scope distinction; we do not claim that no equivalent consequence can be derived elsewhere or that all components are novel.

The related project's [Assumptions.lean](https://github.com/joachimneu/distinct-reciprocal-subset-sums/blob/e51bf855d37c97cc66126b98144804c950f86872/Erdos320/Assumptions.lean) declares four external inputs for its larger asymptotic development; several concrete modular checks use `native_decide`. This does **not** mean each of its elementary lemmas depends on all those inputs. Our scoped module has been audited separately: all 26 theorem closures contain only the standard `propext`, `Classical.choice`, `Quot.sound`. No comparison to the completeness of the larger project's asymptotic result is intended.

No source code from that project is incorporated. The proof implementation here was written independently from the mathematical statement and Mathlib APIs. Similar elementary definitions reflect the same problem. The concrete `(m,p)=(4,2)` family illustrates the absence of a seed bound; as a prime-power family, it is not a new mathematical conclusion.

## Submission status and authorship

Prepared with GPT/Codex assistance by `green3sf`. The current official issue/PR listing was checked through issue 671 without finding a directly matching JSP-000266 submission; such a search does not establish global priority. Public research and proof preparation took place on 17 September 2026.

This is scoped formal evidence, not a request to mark the whole problem formalized, an announced award, or an established entitlement. No recipient identities, recipient allocations or catalog fields are added. The submitter has an interest in recognition of the submitted formal work. Attribution, admissibility, contribution significance and any award remain subject to organizer review.
