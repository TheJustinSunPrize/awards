# Provenance and overlap

This is an OpenAI ChatGPT-assisted formalization prepared under the submitting account's direction. The submitter has a direct interest in the prize review. No independent human verification is claimed.

The mathematical existence of 27-element counterexamples is credited to D. V. Fomin and O. T. Izhboldin, "Sets of multiple sums", Proc. St. Petersburg Math. Soc. 3 (1994), 244-259, following the bibliography and explanatory text in [Formal Conjectures 494](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/494.lean). The original article was not independently inspected in preparing this package.

The displayed positive-integer sets were independently constructed during this work. Direct computation supplies their certificate; no previously published concrete witness or proof text is asserted to be original. The broad structural insight is not asserted as a mathematical discovery.

Compatibility.lean reproduces the two short specification definitions from Formal Conjectures, retaining attribution under Apache-2.0; see LICENSE-APACHE. Main proof code and scripts use the repository's MIT license; see LICENSE. Mathlib is an external dependency with its own notices and license.

Prior work reviewed:
- [Prize PR #23](https://github.com/TheJustinSunPrize/awards/pull/23): power-of-two pair-sum families, six-element triple sums, and general card=2k negative results.
- [Prize PR #127](https://github.com/TheJustinSunPrize/awards/pull/127): Selfridge-Straus positive uniqueness criteria.
- [plby/Erdos494.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos494.lean): card=2k negative result; includes a map-negation proof using Mathlib's powerset-cardinality and multiset-map lemmas. Those library patterns informed the natural-to-complex adapter here.

The reviewed sources do not contain the specific 27-element theorem proved in this package. The search is not exhaustive and does not establish global first-formalization priority. Maintainers should determine overlap and eligible incremental contribution.

Proposed recipient: RECIPIENT-JSP-000399-KZ-A, confirmation pending. Mathematical solvers, statement authors, library developers, and formalizers have distinct roles. No solver reattribution, award allocation, or payment entitlement is proposed.
