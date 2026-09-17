# Sources and attribution

1. T. F. Bloom, [Erdos Problem 1063](https://www.erdosproblems.com/1063) and its
   [discussion thread](https://www.erdosproblems.com/forum/thread/1063), accessed
   17 September 2026. The page records Monier's factorial bound and Stijn
   Cambie's `k*lcm(1,...,k-1)` bound. The latter is discussed in Cambie's comment
   dated 1 October 2025. The page still describes the original problem as open.
2. Erdos, P. and Selfridge, J. L., *Problem 6447*, American Mathematical Monthly
   (1983), p. 710; Monier, J.-M., *Problems and Solutions: Solutions of Advanced
   Problems: 6447*, American Mathematical Monthly 92 (1985), pp. 435-436;
   Guy, R. K., *Unsolved Problems in Number Theory* (2004), Problem B31.
   These bibliographic entries are reproduced from the problem page and Formal
   Conjectures; the original publications were not independently retrieved here.
3. The Formal Conjectures Authors,
   [ErdosProblems/1063.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1063.lean),
   inspected source blob `bda13fc03989bb240293a164c7d70c75dfcc86f9`.
   The exact source blob and natural-number lcm interpretation were checked.
   The package's minimum and target definitions follow this source. Copyright
   and Apache-2.0 attribution are retained; no unproved upstream theorem is
   imported as a proof.
4. The classical prime number theorem, `pi(x) ~ x/log(x)`, is used as a standard
   mathematical input. Its application to the interval in this note is written
   explicitly. This input is not a new result and has not been connected to a
   proved Lean library theorem in this package.
5. Related formalization submissions:
   [PR #56](https://github.com/TheJustinSunPrize/awards/pull/56) (Monier),
   [PR #154](https://github.com/TheJustinSunPrize/awards/pull/154) (Cambie), and
   [PR #406](https://github.com/TheJustinSunPrize/awards/pull/406) (positive
   factorial multiples and Monier). Their public descriptions do not claim
   this note's `O(L_k)` improvement. This bounded check does not establish
   global novelty or priority; further prior-art pointers are requested.

## Contribution disclosure

The original written argument, experiment code, and target-only Lean files
were supplied in a research bundle prepared with ChatGPT assistance. The
publishing account `randyxian08` directs this public research submission.
OpenAI Codex assisted in checking the argument, rerunning the experiments,
inspecting the Lean declarations, preparing the English manuscript/PDF, and
publishing the reproducibility package. This is a self-submission of an
AI-assisted research claim, not an independent referee report.

The package does not assert a confirmed legal recipient identity, prize
entitlement, first-discovery priority, or full resolution of the original
estimation problem. Earlier bounds retain their mathematical authors' credit.
The original input ZIP has SHA-256
`f4e8ff2dbea118310fa4faf8276e50d59643703810e13e57ab8fa21a60f0ca5a`.

Mathematical text, code, and publication additions are provided under the
included Apache-2.0 license, preserving third-party notices.
