# JSP-000912 / Erdős Problem 1099 — independent full formalization submission

This submission requests review of an independently developed Lean formalization of the full main statement of JSP-000912 / Erdős Problem 1099.

## Scope

For every real `α > 1`, the formalization proves the existence of a constant `C` such that for every cutoff `M` there is a positive integer `n ≥ M` for which the sum over **all consecutive positive divisors**

`Σ_i (d_{i+1}/d_i - 1)^α`

is at most `C`.

The strengthened root theorem also requires the witness `n` to be strictly positive. The implementation uses an explicit cofinal construction, controls actual adjacent divisors rather than only an auxiliary grid, and treats the upper half of the divisor list by complementary-divisor reflection.

## Attribution and overlap

The mathematical theorem is due to Michael D. Vose (1984). This implementation was developed with ChatGPT assistance for Ketian Zhang.

**No first-formalization or mathematical-priority claim is made.** After completing and locally verifying this implementation, a separate pre-existing full formalization was found in `plby/lean-proofs`, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, at `src/latest/ErdosProblems/Erdos1099.lean`, credited there to Codex and GPT-5.6 Sol.

This PR is therefore submitted only for review of the independently developed formalization contribution and any recognition the organizers consider appropriate. It does not assert that the contribution is eligible, unique, first, accepted, or entitled to payment.

## Local verification

The complete standalone source was checked with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The final theorem and principal intermediate theorems compiled successfully. The axiom audit reported only:

- `propext`
- `Classical.choice`
- `Quot.sound`

No project-specific mathematical axioms, `sorry`, `admit`, or `native_decide` are used in the checked source.

The source package is intentionally not represented here as independently verified by the prize organizers. Contributor-side compilation is evidence for reproduction, not an award decision.

## Requested review

Please assess:

1. full-statement correspondence for JSP-000912 / Erdős 1099;
2. the independently developed proof architecture and formalization contribution;
3. overlap with the earlier `plby/lean-proofs` implementation;
4. attribution and any contribution eligibility under the published prize rules.

No catalog status, candidate record, recipient confirmation, award decision, or payment status is changed by this submission.
