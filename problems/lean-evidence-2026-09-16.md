# Existing public Lean evidence: 16 September 2026

This is a catalog correction and source register, not a new mathematical proof, a new Lean formalization, a recipient nomination, or an award claim. It records work published by the original contributors and links existing evidence registrations. The compiler of this register does not claim authorship, first-formalization priority, or a share of an award for any proof listed here.

The reviewed catalog base is [`f4e7173d89dfe91022a185427d63452c8ffbf6ae`](https://github.com/TheJustinSunPrize/awards/tree/f4e7173d89dfe91022a185427d63452c8ffbf6ae). This register covers **78 records** with individually located, pinned sources. It is not an exhaustive audit of every catalog entry or every file in an external repository.

## How to read this register

- **Reported; source located** replaces an unqualified negative or source-not-located label when a concrete public implementation has been found. Completion, statement correspondence, all transitive dependencies, and any reported replay still require review. This label does not certify a complete proof.
- **Pending verification** is a problem-bank screening flag, not acceptance into a candidate pool or permission to claim payment. These records remain **Unavailable** while that screening review is pending.
- **JSP-000465** is linked to OpenAI's official published implementation and formalization metadata, covering the same compactness counterexample already recognized under the related JSP-000174 entry. Its catalog screening flags follow the existing **Solved / Yes / Yes / Unclaimed** convention; this is not a claim by the submitter.
- This correction inspected source statements, scope, attribution and public evidence. It did **not** independently rebuild these third-party proof projects or rerun their kernels/comparators. Reproduction results in the linked issues or archives belong to their respective reporters.
- Mathematical and formalization credits below are reported from the linked source headers or metadata, with discrepancies retained. A repository owner or evidence reporter is not automatically a proof author. AI-assisted third-party repositories are distinguished from official OpenAI publication.
- Existing issue registrations are credited and linked rather than republished as new proof submissions. New proof intake PRs, including the separate JSP-000690 submission, remain in their existing review threads.

## Sources and scope by record

<a id="jsp-000139"></a>

### JSP-000139 / Erdős 133

[Catalog record](catalog-0101-0200.md#JSP-000139) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos133.lean)

- **Recorded scope:** For all n >= 64, the minimum possible maximum degree of a triangle-free n-vertex graph of diameter at most two is between sqrt(n)-1 and 4 sqrt(n).
- **Mathematical credits reported by the source:** D. Hanson; K. Seyffarth.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** The source expands the names incorrectly; issue #22 cites the university bibliography for Denis Hanson and Karen Seyffarth. Initials retained.
- **Limits and review status:** The graph extremum is minimum-achievable maximum degree; no exact extremal formula is claimed. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000183"></a>

### JSP-000183 / Erdős 193

[Catalog record](catalog-0101-0200.md#JSP-000183) · [Pinned Lean source](https://github.com/ekalvi/erdos-193/blob/b156ed0039b5c1b028e210aa80d28d2644fad976/formal/Hilbert193/Hilbert193/Continuity.lean)

- **Recorded scope:** An infinite injective Z^3 walk has a fixed finite step-vector set and no collinear triple.
- **Mathematical credits reported by the source:** Stijn Cambie; Erik Kalviainen.
- **Formalization credits reported by the source:** Stijn Cambie; Erik Kalviainen.
- **Attribution qualification:** Pinned CITATION.cff explicitly requests this citation for the construction or formalization.
- **Limits and review status:** The issue mathematically audits the coordinate collinearity predicate; no separate Mathlib affine-Collinear bridge was compiled. No unit-step variant. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000194"></a>

### JSP-000194 / Erdős 210

[Catalog record](catalog-0101-0200.md#JSP-000194) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos210.lean)

- **Recorded scope:** The minimum ordinary-line count satisfies n <= 10 f(n) and f(n) <= n-1 for n >= 4, hence has linear order.
- **Mathematical credits reported by the source:** L. M. Kelly; W. O. J. Moser.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; Boris Alexeev.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Does not claim the sharp Kelly-Moser or Green-Tao constants. Source has two differing formal-author notices; preserve both. No extra affine geometry bridge compiled by the issue reporter. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000203"></a>

### JSP-000203 / Erdős 225

[Catalog record](catalog-0201-0300.md#JSP-000203) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos225.lean)

- **Recorded scope:** For a positive-degree polynomial with nonzero leading and constant coefficients, all roots on the unit circle and maximum boundary norm 1, its boundary norm integral is at most 4; the real-angular-root bridge is proved.
- **Mathematical credits reported by the source:** E. B. Saff; T. Sheil-Small.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Published nondegenerate formulation only. Do not present as a proof of the vacuous monomial-inclusive reading; q>0 generalization and equality classification are not covered. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000204"></a>

### JSP-000204 / Erdős 227

[Catalog record](catalog-0201-0300.md#JSP-000204) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos227.lean)

- **Recorded scope:** A transcendental entire power series has maximum-term / maximum-modulus ratio tending to 1/2 over all real radii, refuting the assertion that an existing limit must be zero.
- **Mathematical credits reported by the source:** J. Clunie; W. K. Hayman.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** A counterexample to the proposed implication, not a classification of all limits; no extra compiled analytic equivalence bridge was reported. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000281"></a>

### JSP-000281 / Erdős 339

[Catalog record](catalog-0201-0300.md#JSP-000281) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos339.lean)

- **Recorded scope:** Every asymptotic additive basis of order r has positive lower density of sums of exactly r pairwise distinct members.
- **Mathematical credits reported by the source:** Norbert Hegyvári; François Hennecart; Alain Plagne.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Does not claim the distinct positive-upper-density variant. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000288"></a>

### JSP-000288 / Erdős 346

[Catalog record](catalog-0201-0300.md#JSP-000288) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos346.lean)

- **Recorded scope:** A strictly increasing positive sequence is complete after every finite deletion and incomplete after every infinite deletion, has consecutive ratios >= 6/5, and has nonconvergent ratios.
- **Mathematical credits reported by the source:** Liam Price; GPT-5.5.
- **Formalization credits reported by the source:** Liam Price; GPT-5.5.
- **Attribution qualification:** Thin entry header attributes a formalized proof claim to Liam Price and GPT-5.5; referenced provenance README absent at pinned tree. Does not resolve conflicting older model labels.
- **Limits and review status:** Does not settle the variant that assumes ratio convergence. Referenced upstream provenance README was not present in the pinned tree. Historical 2026-09-11 note should remain historical, with a new dated correction. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000331"></a>

### JSP-000331 / Erdős 402

[Catalog record](catalog-0301-0400.md#JSP-000331) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos402.lean)

- **Recorded scope:** erdos_402: there is N₀ such that every nonempty positive-integer finite set A of cardinality at least N₀ contains a,b with gcd(a,b)≤a/&#124;A&#124;, interpreted in ℚ.
- **Mathematical credits reported by the source:** R. Balasubramanian; K. Soundararajan.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Header attributes mathematics to R. Balasubramanian and K. Soundararajan and the statement to Formal Conjectures authors; the JSP bibliography additionally cites Szegedy and Zaharescu.
- **Limits and review status:** Not independently recompiled during this catalog audit. This is the sufficiently-large statement in the JSP entry. It is not a proof of the stronger all-cardinalities Erdős variant. Some finite helper proofs use native_decide; final axiom dependency closure was not replayed.

<a id="jsp-000359"></a>

### JSP-000359 / Erdős 440

[Catalog record](catalog-0301-0400.md#JSP-000359) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean)

- **Recorded scope:** For every increasing positive integer sequence, adjacent-LCM count N(x) is O(sqrt(x)); the exact series upper limsup constant is attained; normalized liminf <= 1 and is attained by another sequence.
- **Mathematical credits reported by the source:** Paul Erdős; Endre Szemerédi.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Natural-number thresholds; no separately compiled real-threshold bridge or decimal approximation of the exact series constant. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000364"></a>

### JSP-000364 / Erdős 449

[Catalog record](catalog-0301-0400.md#JSP-000364) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos449.lean)

- **Recorded scope:** For every K > 0 there is a set of positive existing natural density on which the close-divisor-pair count r(n), using d1 < d2 < 2 d1, exceeds K tau(n).
- **Mathematical credits reported by the source:** Kevin Ford.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** No natural density claim for the entire superlevel set. The final theorem has no Equation7 hypothesis despite a conditional development in an import. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/22). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000377"></a>

### JSP-000377 / Erdős 465

[Catalog record](catalog-0301-0400.md#JSP-000377) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos465.lean)

- **Recorded scope:** For each delta > 0, planar point sets in a radius-X disk with pairwise distances delta-away from integers have cardinality <= C(delta) sqrt(X), X >= 1; consequently N(X,delta)=o(X).
- **Mathematical credits reported by the source:** Sergei V. Konyagin.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** The constant depends on delta; no matching lower bound. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000378"></a>

### JSP-000378 / Erdős 466

[Catalog record](catalog-0301-0400.md#JSP-000378) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos466.lean)

- **Recorded scope:** Arbitrarily large planar point sets have every distance more than 1/10 away from every integer; the explicit points are (2^m,4^m).
- **Mathematical credits reported by the source:** Ronald Graham.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** One fixed separation; not every prescribed separation. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000383"></a>

### JSP-000383 / Erdős 471

[Catalog record](catalog-0301-0400.md#JSP-000383) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos471.lean)

- **Recorded scope:** erdos_471: there exists a finite set of primes whose generations, adjoining prime sums of three pairwise distinct existing primes, have unbounded cardinalities.
- **Mathematical credits reported by the source:** Luka Mrazović; Vjekoslav Kovač; Noga Alon.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Source header says Luka Mrazović, whereas current JSP prose says Rudi Mrazović; this discrepancy is retained for review rather than silently normalized.
- **Limits and review status:** Not independently recompiled during this catalog audit. Read main theorem and selected Vinogradov/circle-method inputs, not every transitive analytic dependency. Does not assert the particular seed {3,5,7,11}.

<a id="jsp-000385"></a>

### JSP-000385 / Erdős 473

[Catalog record](catalog-0301-0400.md#JSP-000385) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos473.lean)

- **Recorded scope:** erdos_473: there is a bijection a:ℕ≃ℕ+ such that a(n)+a(n+1) is prime for every n.
- **Mathematical credits reported by the source:** A. M. Odlyzko.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. Read finite-extension-to-bijection construction and selected analytic inputs; external BoundedGaps dependency was not fully audited. Does not assert every finite-n permutation variant.

<a id="jsp-000391"></a>

### JSP-000391 / Erdős 482

[Catalog record](catalog-0301-0400.md#JSP-000391) · [Pinned Lean source](https://github.com/gotrevor/lean-gallery/blob/efc72e14c2030842a44dbc7e42850981886fdd03/LeanGallery/NumberTheory/Erdos482/Statement.lean)

- **Recorded scope:** statement_erdos482_resolution / General.erdos482_resolution: every real w>0 and base g≥2 admit an explicit Graham–Pollak-type recurrence reading its base-g digits; includes original binary √2 theorem and bridge to Mathlib Real.digits.
- **Mathematical credits reported by the source:** Graham–Pollak (binary √2 result); Thomas Stoll (general-base resolution).
- **Formalization credits reported by the source:** Trevor Morris.
- **Limits and review status:** Not independently recompiled during this catalog audit. Statement and underlying general theorem read. Author metadata reports standard-three-axiom guards/comparator checks; these were not independently replayed. Additional impossibility-frontier claims are outside this catalog correction.
- **Attribution source:** [Source](https://github.com/gotrevor/lean-gallery/blob/efc72e14c2030842a44dbc7e42850981886fdd03/formalization.yaml).

<a id="jsp-000419"></a>

### JSP-000419 / Erdős 523

[Catalog record](catalog-0401-0500.md#JSP-000419) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos523.lean)

- **Recorded scope:** For independent fair random signs, the maximum circle modulus of the polynomial with coefficients 0 through n, normalized by sqrt(n log n), converges almost surely to 1 along the full sequence.
- **Mathematical credits reported by the source:** Gábor Halász.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** The explicitly defined fair-sign probability measure; no alternate distributions claimed. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000440"></a>

### JSP-000440 / Erdős 549

[Catalog record](catalog-0401-0500.md#JSP-000440) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos549.lean)

- **Recorded scope:** A double-star counterexample with bipartition sizes 16 and 32 refutes the universal two-color tree Ramsey formula R(T)=4k-1 via a coloring of K_63.
- **Mathematical credits reported by the source:** Sergey Norin; Yelena Sun; Yufei Zhao.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; OpenAI Codex.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Does not determine the Ramsey number of every tree in this class. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000448"></a>

### JSP-000448 / Erdős 557

[Catalog record](catalog-0401-0500.md#JSP-000448) · [Pinned Lean source](https://github.com/Jayyhk/erdos-lean/blob/edb4c93f751fc14afd69f14f13a3fc307760a922/problems/557/Erdos557.lean)

**Superseded catalog note:** The previous record said the standalone source had not been located. A pinned source and a reported compatibility port are now linked below. The previous related-proof credit does not establish authorship of this newly located source.

<details><summary>Previous source-not-located field (retained as history)</summary>

Reported; standalone Lean source not located. The reviewed commentary derives this problem from the tree-embedding result in [JSP-000439](catalog-0401-0500.md#JSP-000439).<br>Formalization contributors: For the related proof of JSP-000439 only: GPT-6 Astra (Lean proof); Tom Adamczewski directed preparation of the public repository. This does not establish separate formalization authorship for JSP-000448.

</details>

- **Recorded scope:** For every positive color count k and every tree on t+1 vertices, m >= k(t+1)+2 guarantees a monochromatic non-induced copy in every k-coloring of K_m.
- **Mathematical credits reported by the source:** Not individually identified in the pinned main file; see the source and attribution qualification below.
- **Formalization credits reported by the source:** No explicit personal author header was located; repository ownership is not treated as proof authorship.
- **Attribution qualification:** Public source: Jayyhk/erdos-lean. No explicit personal author header in fetched main file; do not infer identity from repository owner. Issue #16 documents attributed compatibility port.
- **Limits and review status:** Issue #16 verifies a five-hunk Lean 4.33 compatibility port, not unchanged original source. Original project specifies Lean 4.28; no independent original-environment build here. Main source includes a section about Problem 548 but also exports Erdos557.erdos_557. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000450"></a>

### JSP-000450 / Erdős 559

[Catalog record](catalog-0401-0500.md#JSP-000450) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos559.lean)

- **Recorded scope:** No constant linearly bounds ordinary two-color size-Ramsey numbers of all graphs of maximum degree at most 3 by their vertex count.
- **Mathematical credits reported by the source:** Vojtěch Rödl; Endre Szemerédi.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; OpenAI Codex.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Not induced Ramsey numbers or stronger quantitative growth rates. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000464"></a>

### JSP-000464 / Erdős 574

[Catalog record](catalog-0401-0500.md#JSP-000464) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos574.lean)

- **Recorded scope:** For k=3, a family of bipartite C6-free graphs disproves the proposed asymptotic for ex(n;{C_(2k-1),C_(2k)}).
- **Mathematical credits reported by the source:** Felix Lazebnik; Vasiliy Ustimenko; Andrew Woldar.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** A counterexample is sufficient to refute the universal proposal; not the exact extremal function for all k. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000465"></a>

### JSP-000465 / Erdős 575

[Catalog record](catalog-0401-0500.md#JSP-000465) · [Pinned Lean source](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean)

- **Recorded scope:** quantitativeCompactnessCounterexample and compactnessCounterexample_bigO: a finite nonempty family of connected bipartite cyclic graphs has joint extremal number O(n^(21/16)), while every member has extremal number Ω(n^(4/3)); the compactness assertion is false.
- **Mathematical credits reported by the source:** An internal OpenAI model (as identified by the catalog and associated release).
- **Formalization credits reported by the source:** OpenAI (publishing organization; individual formalization authors are not named in this source).
- **Limits and review status:** Not independently recompiled during this catalog audit. Read the actual solution and challenge/configuration; no sorry or custom axiom was found in the solution. Challenge-file sorry is an interface placeholder. Comparator configuration is not an independently reproduced run.
- **Attribution source:** [Source](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/README.md).

<a id="jsp-000468"></a>

### JSP-000468 / Erdős 578

[Catalog record](catalog-0401-0500.md#JSP-000468) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos578.lean)

- **Recorded scope:** A uniformly chosen labelled simple graph on 2^d vertices contains a spanning d-cube with probability tending to 1.
- **Mathematical credits reported by the source:** Oliver Riordan.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** The independent-edge probability is p=1/2; the stronger all-p>1/4 result is not covered. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000471"></a>

### JSP-000471 / Erdős 581

[Catalog record](catalog-0401-0500.md#JSP-000471) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos581.lean)

- **Recorded scope:** For all natural m, the maximum guaranteed edge count f(m) in a bipartite subgraph of every triangle-free graph with m edges obeys m/2 + m^(4/5)/1024 <= f(m) <= m/2 + 1024 m^(4/5).
- **Mathematical credits reported by the source:** Noga Alon.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Order of surplus over m/2, not optimal constants. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000490"></a>

### JSP-000490 / Erdős 603

[Catalog record](catalog-0401-0500.md#JSP-000490) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos603.lean)

- **Recorded scope:** For every cardinal C there is an arbitrary family of countably infinite sets, with pairwise intersections never size 2, such that every C-coloring of the union has a monochromatic member.
- **Mathematical credits reported by the source:** Przemek Chojecki; GPT-5.4 Pro.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** The family and union are not assumed countable; this is not a countable-family restriction. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000492"></a>

### JSP-000492 / Erdős 605

[Catalog record](catalog-0401-0500.md#JSP-000492) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos605.lean)

- **Recorded scope:** There is a fixed sphere and f(n) tending to infinity such that n distinct points on it have at least n f(n) unordered pairs at one positive distance.
- **Mathematical credits reported by the source:** Paul Erdős; Dean Hickerson; János Pach.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Uses the unit sphere and distance sqrt(2); no statement for every prescribed sphere diameter. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000494"></a>

### JSP-000494 / Erdős 607

[Catalog record](catalog-0401-0500.md#JSP-000494) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos607.lean)

- **Recorded scope:** The count F(n) of sets of distinct line multiplicities of planar n-point configurations is eventually at most exp(68 sqrt(n)).
- **Mathematical credits reported by the source:** Endre Szemerédi; William T. Trotter Jr..
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; OpenAI Codex.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Counts sets, not multisets/sequences (JSP-601); no matching lower bound. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000506"></a>

### JSP-000506 / Erdős 625

[Catalog record](catalog-0501-0600.md#JSP-000506) · [Pinned Lean source](https://github.com/SamPetkov/Erdos/blob/824e4b609466d2e26b216a76ecf103184dac2663/625/formalization/Erdos625.lean)

- **Recorded scope:** The source declares Erdos625.erdos625: for G(n,1/2), probability tends to one along the full natural-number sequence that χ−ζ ≥ ((ln 2)^2/4) ln(200/153) · n/(ln n)^3.
- **Mathematical credits reported by the source:** Samuil Petkov.
- **Formalization credits reported by the source:** Samuil Petkov.
- **Attribution qualification:** The manuscript explicitly says neither AI system is an author. Samuil Petkov directed, reviewed, and integrated the work; do not list the systems as coauthors.
- **Limits and review status:** Not independently recompiled or kernel-replayed during this catalog audit. This entry records the uniform /4 source statement, not the stronger nonconstant phase-resolved coefficient A_4(delta_n). Independent reproduction and review remain pending; published replay reports are version-specific and were not independently rerun.
- **Coefficient correction:** The formalization note in the pinned manuscript reports /32, but the actual [constant definition](https://github.com/SamPetkov/Erdos/blob/824e4b609466d2e26b216a76ecf103184dac2663/625/formalization/Erdos625/Foundation.lean), [probability target](https://github.com/SamPetkov/Erdos/blob/824e4b609466d2e26b216a76ecf103184dac2663/625/formalization/Erdos625/Target.lean), and [final theorem](https://github.com/SamPetkov/Erdos/blob/824e4b609466d2e26b216a76ecf103184dac2663/625/formalization/Erdos625/Section15FinalInstantiation.lean) at the same source pin use /4. Corrected following [randyxian08's source audit](https://github.com/TheJustinSunPrize/awards/pull/40#issuecomment-5697271091); this acknowledges the source correction, not independent proof verification.
- **Attribution source:** [Source](https://github.com/SamPetkov/Erdos/blob/824e4b609466d2e26b216a76ecf103184dac2663/625/arxiv/main.tex).

<a id="jsp-000513"></a>

### JSP-000513 / Erdős 632

[Catalog record](catalog-0501-0600.md#JSP-000513) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos632.lean)

- **Recorded scope:** erdos_632_counterexample and not_erdos_632: a finite graph is (4:1)-choosable but not (8:2)-choosable; choosability quantifies arbitrary color types and list assignments.
- **Mathematical credits reported by the source:** Zdeněk Dvořák; Xiaolan Hu; Jean-Sébastien Sereni.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. Read the main module and all five local support modules. Static checks found no sorry/custom axiom in those files; no independent kernel replay.
- **Additional registration qualification:** The final uniform-list graph is not merely the intermediate 37-vertex gadget; no parameter classification. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000532"></a>

### JSP-000532 / Erdős 656

[Catalog record](catalog-0501-0600.md#JSP-000532) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos656.lean)

- **Recorded scope:** Every positive-upper-density subset A of N contains an infinite B subset A and a fixed integer t with b+b_prime+t in A for all distinct b,b_prime in B.
- **Mathematical credits reported by the source:** Bryna Kra; Joel Moreira; Florian K. Richter; Donald Robertson.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; OpenAI Codex.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Distinct-pair sums; no requirement for diagonal sums 2b, and no untranslated version. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000539"></a>

### JSP-000539 / Erdős 664

[Catalog record](catalog-0501-0600.md#JSP-000539) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos664.lean)

- **Recorded scope:** For c=2/5 and every K, a family of subsets of an n-point set has each member size > c sqrt(n), pairwise intersections <=1, and every transversal meets some member more than K times.
- **Mathematical credits reported by the source:** Noga Alon.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Per-member transversal bound; not a bound on total transversal size, nor the separate full finite geometry variant. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000562"></a>

### JSP-000562 / Erdős 690

[Catalog record](catalog-0501-0600.md#JSP-000562) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean)

- **Recorded scope:** The natural-density distribution of the kth smallest distinct prime factor has an exact formula; it is unimodal for k=1,2,3 and not unimodal for 4<=k<=20.
- **Mathematical credits reported by the source:** Stijn Cambie.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; OpenAI Codex.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** No conclusion for k>20. This refutes universal unimodality but is a bounded-k classification, and must not be labeled an all-k classification. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000572"></a>

### JSP-000572 / Erdős 702

[Catalog record](catalog-0501-0600.md#JSP-000572) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos702.lean)

- **Recorded scope:** For each fixed k>=4 and sufficiently large n, every k-uniform family with more than binomial(n-2,k-2) members has two members meeting in exactly one point; also gives the n=5,k=4 counterexample to the all-n version.
- **Mathematical credits reported by the source:** Péter Frankl.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** The positive result is eventual in n, not every n. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000575"></a>

### JSP-000575 / Erdős 705

[Catalog record](catalog-0501-0600.md#JSP-000575) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos705.lean)

- **Recorded scope:** For every girth threshold there is a faithfully embedded Euclidean planar unit-distance graph that is not 3-colorable.
- **Mathematical credits reported by the source:** Paul O'Donnell.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; OpenAI Codex.
- **Attribution qualification:** Credits transcribed from pinned source notices; repository owner is not asserted to be an author.
- **Limits and review status:** Planar means points in the Euclidean plane, not graph-theoretically planar; no exact four-color upper bound is asserted. We did not compile or replay this source; successful compilation, target replay, and standard-axiom outputs are reported by the issue author, not reproduced here.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/16). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000598"></a>

### JSP-000598 / Erdős 730

[Catalog record](catalog-0501-0600.md#JSP-000598) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos730.lean)

- **Recorded scope:** erdos_730_consecutive: infinitely many n have the same prime factors in C(2n,n) and C(2n+2,n+1); erdos_730 also proves infinitely many distinct parameter pairs.
- **Mathematical credits reported by the source:** Liam Price; Tomodovodoo; Will Blair; GPT Pro.
- **Formalization credits reported by the source:** Will Blair; Codex; Claude Code.
- **Limits and review status:** Not independently recompiled during this catalog audit. Read main theorem and selected full-density/Mertens/PNT-AP inputs; no complete transitive replay or independent registry-log validation. The original problem has an infinitude quantifier missing from the JSP summary.

<a id="jsp-000622"></a>

### JSP-000622 / Erdős 758

[Catalog record](catalog-0601-0700.md#JSP-000622) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos758.lean)

- **Recorded scope:** erdos_758 proves z(12)=4, the maximum cochromatic number of a 12-vertex graph, using every_graph_on_twelve_colorable_four and a matching lower witness.
- **Mathematical credits reported by the source:** Bhavik Mehta.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. Main theorem scope checked; no complete transitive audit or certificate replay.

<a id="jsp-000628"></a>

### JSP-000628 / Erdős 767

[Catalog record](catalog-0601-0700.md#JSP-000628) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos767.lean)

- **Recorded scope:** erdos_767: for k>0 and n≥3k+3, the maximum edge count without a cycle having k incident chords is (k+1)n−(k+1)^2.
- **Mathematical credits reported by the source:** Tao Jiang.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. Main theorem and two support imports identified; complete transitive dependency audit not performed.

<a id="jsp-000633"></a>

### JSP-000633 / Erdős 772

[Catalog record](catalog-0601-0700.md#JSP-000633) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean)

- **Recorded scope:** Bounded two-term representation multiplicities imply a Sidon subset of order at least &#124;A&#124;^(2/3), and the stated two asymptotic lower bounds.
- **Mathematical credits reported by the source:** Noga Alon; Paul Erdős.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The source uses ordered representation counts and a capped H(k,n) for the empty admissible class; an unordered bound k translates to an ordered bound 2k+1. Other results of the original paper are not claimed. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000641"></a>

### JSP-000641 / Erdős 781

[Catalog record](catalog-0601-0700.md#JSP-000641) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos781.lean)

- **Recorded scope:** The least interval forcing a length-k monochromatic increasing nonincreasing-gap sequence has cubic order; this refutes the proposed exact quadratic formula.
- **Mathematical credits reported by the source:** Noga Alon; Joel Spencer.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Cubic bounds hold for k>=2^50 (upper bound separately for k>=2); no optimal cubic constant. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/29). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000657"></a>

### JSP-000657 / Erdős 800

[Catalog record](catalog-0601-0700.md#JSP-000657) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos800.lean)

- **Recorded scope:** Graphs with no adjacent vertices both of degree at least three have Ramsey number at most 12 times their vertex count.
- **Mathematical credits reported by the source:** Noga Alon.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** No claim to an optimal linear constant. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000658"></a>

### JSP-000658 / Erdős 801

[Catalog record](catalog-0601-0700.md#JSP-000658) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos801.lean)

- **Recorded scope:** For all sufficiently large n, independence number at most floor(sqrt n) forces a subset of at most floor(sqrt n) vertices with induced edge count at least a constant multiple of sqrt(n) log n.
- **Mathematical credits reported by the source:** Noga Alon.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Retain the sufficiently-large-n quantifier and absolute implicit constant. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000663"></a>

### JSP-000663 / Erdős 806

[Catalog record](catalog-0601-0700.md#JSP-000663) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos806.lean)

- **Recorded scope:** Uniformly for all A in {1,...,n} of size at most sqrt n, a set B of integers of size o(sqrt n) can satisfy A subset B+B.
- **Mathematical credits reported by the source:** Noga Alon; Boris Bukh; Benny Sudakov.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** No claim to the stronger quantitative O(sqrt(n) log log n / log n) rate. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000673"></a>

### JSP-000673 / Erdős 816

[Catalog record](catalog-0601-0700.md#JSP-000673) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos816.lean)

- **Recorded scope:** erdos_816_of_at_least: for n≥2, a graph on 2n+1 vertices with at least n²+n+1 edges has distinct equal-degree endpoints joined by a three-edge path; exact-edge theorem also exported.
- **Mathematical credits reported by the source:** Kaizhe Chen; Jie Ma; Zhen Liu; Qinghou Zeng.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. n≥2 is the effective range; the n=1 triangle cannot contain a three-edge simple path. All transitive dependencies were not independently rebuilt.
- **Additional registration qualification:** n=1 is excluded because K3 is a counterexample; the three-edge path has four distinct vertices. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000688"></a>

### JSP-000688 / Erdős 832

[Catalog record](catalog-0601-0700.md#JSP-000688) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos832.lean)

- **Recorded scope:** The proposed eventual edge lower bound and equality characterization for all uniformities r >= 3 is false; counterexamples use r=4 and arbitrarily large chromatic number.
- **Mathematical credits reported by the source:** Noga Alon.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The r=3 specialization and an exact general extremal function are not resolved by this result. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000689"></a>

### JSP-000689 / Erdős 833

[Catalog record](catalog-0601-0700.md#JSP-000689) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean)

- **Recorded scope:** Every finite r-uniform hypergraph of chromatic number three has a vertex of degree at least (1+c)^r for one absolute c>0 and all r>=2.
- **Mathematical credits reported by the source:** Paul Erdős; László Lovász.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Does not determine the exact extremal function f(r). This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000715"></a>

### JSP-000715 / Erdős 863

[Catalog record](catalog-0701-0800.md#JSP-000715) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos863.lean)

- **Recorded scope:** For r>=2, if the stated square-root asymptotic constants for bounded sum and difference multiplicities exist, the difference constant is strictly smaller than the sum constant.
- **Mathematical credits reported by the source:** Boon Suan Ho; Javier Cilleruelo; Imre Ruzsa; Carlos Trujillo; GPT-5.4 Pro.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Existence of the two asymptotic constants remains an explicit hypothesis, as in the question. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000731"></a>

### JSP-000731 / Erdős 880

[Catalog record](catalog-0701-0800.md#JSP-000731) · [Pinned Lean source](https://github.com/gotrevor/lean-gallery/blob/efc72e14c2030842a44dbc7e42850981886fdd03/LeanGallery/Combinatorics/Erdos880/Statement.lean)

- **Recorded scope:** erdos_880_order_two: restricted sums of an order-2 additive basis have eventually bounded gaps ≤2. erdos_880: for every h≥3 there is an order-h additive basis with arbitrarily long gaps in sums of at most h distinct elements; exact-order strengthened theorem also included.
- **Mathematical credits reported by the source:** Norbert Hegyvári; François Hennecart; Alain Plagne.
- **Formalization credits reported by the source:** Trevor Morris for the primary gotrevor version; Codex and GPT-5.6 Sol for the additional plby version.
- **Limits and review status:** Not independently recompiled during this catalog audit. Designated statement surface read; author-reported AxiomGuard/comparator checks were not independently rerun. Auxiliary open questions about restricted orders are outside the catalog correction. Issue #19 reports replay of the additional plby version, not the primary gotrevor source linked above.
- **Additional registration qualification:** The restricted and unrestricted sumsets allow at most the indicated number of terms. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.
- **Additional pinned source:** [Source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos880.lean).
- **Attribution source:** [Source](https://github.com/gotrevor/lean-gallery/blob/efc72e14c2030842a44dbc7e42850981886fdd03/formalization.yaml).

<a id="jsp-000745"></a>

### JSP-000745 / Erdős 894

[Catalog record](catalog-0701-0800.md#JSP-000745) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos894.lean)

- **Recorded scope:** Every positive lacunary natural sequence admits a finite coloring with no monochromatic difference in that sequence.
- **Mathematical credits reported by the source:** Yuval Peres; Wilhelm Schlag.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The selected theorem is over natural numbers with guarded positive differences; no optimal color-count refinement is claimed. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000746"></a>

### JSP-000746 / Erdős 895

[Catalog record](catalog-0701-0800.md#JSP-000746) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos895.lean)

- **Recorded scope:** Every triangle-free graph on {1,...,n}, n>=18, has distinct independent vertices a,b,a+b.
- **Mathematical credits reported by the source:** Ben Barber.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Sufficiency of 18 only; no 17-vertex counterexample or stronger Hindman-set theorem is claimed. Replay requires the linked CNF/LRAT certificate files. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000751"></a>

### JSP-000751 / Erdős 903

[Catalog record](catalog-0701-0800.md#JSP-000751) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos903.lean)

- **Recorded scope:** A pairwise balanced design on p^2+p+1 points with more than p^2+p+1 blocks has at least p additional blocks.
- **Mathematical credits reported by the source:** Paul Erdős; Joel Fowler; Vera T. Sós; Richard Wilson.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The design definition excludes empty and singleton blocks; no stronger block-count classification is claimed. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000759"></a>

### JSP-000759 / Erdős 915

[Catalog record](catalog-0701-0800.md#JSP-000759) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos915.lean)

- **Recorded scope:** A graph on 17 vertices and 41 edges with no five internally vertex-disjoint paths between a pair refutes the proposed universal edge threshold.
- **Mathematical credits reported by the source:** Bo Sørensen; Carsten Thomassen.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** This is the internally vertex-disjoint version; no positive edge-disjoint theorem or sharp count is claimed. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000769"></a>

### JSP-000769 / Erdős 926

[Catalog record](catalog-0701-0800.md#JSP-000769) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos926.lean)

- **Recorded scope:** For each k>=4, the extremal number of the stated common-center subdivision H_k is O_k(n^(3/2)).
- **Mathematical credits reported by the source:** Zoltán Füredi.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Implicit constants may depend on k; no optimal exponent/constant claim beyond the displayed upper bound. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000788"></a>

### JSP-000788 / Erdős 948

[Catalog record](catalog-0701-0800.md#JSP-000788) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos948.lean)

- **Recorded scope:** For every prescribed growth rate and nonempty finite palette, there is a coloring meeting all colors on finite sums of every qualifying increasing sequence; this negates the proposed omission property.
- **Mathematical credits reported by the source:** Lisa Price; GPT-5.5 Pro.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Source header names Lisa Price whereas the catalog and primary announcement name Liam Price. Preserve the discrepancy and do not infer identity. Growth is infinitely often; separate integer/natural variants are present. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/19). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000799"></a>

### JSP-000799 / Erdős 960

[Catalog record](catalog-0701-0800.md#JSP-000799) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos960.lean)

- **Recorded scope:** erdos_960: for r≥3, k≥4 and n≥72, f(r,k,n) is at least n²/12−(10/3)n+1 and at most the displayed Turán quadratic bound; consequently f is neither o(n²) nor O(n).
- **Mathematical credits reported by the source:** Boris Alexeev; Matthew Putterman; Mehtaab Sawhney; Mark Sellke; Gregory Valiant; OpenAI internal model.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. Read the general-parameter theorem, not only a finite construction; no full geometry/import closure validation.

<a id="jsp-000810"></a>

### JSP-000810 / Erdős 977

[Catalog record](catalog-0801-0900.md#JSP-000810) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos977.lean)

- **Recorded scope:** The largest prime factor of 2^n-1 divided by n tends to infinity along all natural n.
- **Mathematical credits reported by the source:** C. L. Stewart.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** No claim to Stewart quantitative refinement or the separate n!+1 problem. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000821"></a>

### JSP-000821 / Erdős 988

[Catalog record](catalog-0801-0900.md#JSP-000821) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos988.lean)

- **Recorded scope:** The minimum spherical-cap discrepancy of n points on the two-sphere tends to infinity.
- **Mathematical credits reported by the source:** Wolfgang M. Schmidt.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Only the two-sphere, not the higher-dimensional generalization or optimal discrepancy constant. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000825"></a>

### JSP-000825 / Erdős 992

[Catalog record](catalog-0801-0900.md#JSP-000825) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos992.lean)

- **Recorded scope:** One fixed increasing integer sequence has discrepancy at least c sqrt(N log N) infinitely often for almost every scale factor in [0,1], disproving both proposed smaller bounds.
- **Mathematical credits reported by the source:** István Berkes; Walter Philipp.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Almost every scale factor and infinitely many N, not every scale factor or every large N. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000838"></a>

### JSP-000838 / Erdős 1006

[Catalog record](catalog-0801-0900.md#JSP-000838) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1006.lean)

- **Recorded scope:** A finite graph with neither triangles nor four-cycles has no acyclic orientation that remains acyclic after every single-edge reversal.
- **Mathematical credits reported by the source:** Jaroslav Nešetřil; Vojtěch Rödl.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Only girth greater than four, not arbitrary prescribed girth. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000845"></a>

### JSP-000845 / Erdős 1015

[Catalog record](catalog-0801-0900.md#JSP-000845) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1015.lean)

- **Recorded scope:** The exact eventual monochromatic-clique packing remainder is determined, together with the optimal residue-independent eventual bound and both requested asymptotic negations.
- **Mathematical credits reported by the source:** S. A. Burr; Paul Erdős; Joel Spencer.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Uses the intended sufficiently-large host-order interpretation and distinguishes inclusive remainder from strict threshold conventions; all four targets listed in issue #24 are needed for all conclusions. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000851"></a>

### JSP-000851 / Erdős 1021

[Catalog record](catalog-0801-0900.md#JSP-000851) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1021.lean)

- **Recorded scope:** For every fixed k>=3, the extremal number of the one-subdivision of K_k has a positive power saving below n^(3/2).
- **Mathematical credits reported by the source:** Oliver Janzer.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Constants and saving may depend on k; no matching lower bound or optimal saving. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000857"></a>

### JSP-000857 / Erdős 1031

[Catalog record](catalog-0801-0900.md#JSP-000857) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1031.lean)

- **Recorded scope:** For all sufficiently large n, a graph with homogeneous-set size less than 10 log n has an induced nonempty, noncomplete regular subgraph on at least c log n vertices.
- **Mathematical credits reported by the source:** Hans Jürgen Prömel; Vojtěch Rödl.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Retain the strict homogeneous-set bound, coefficient 10, and sufficiently-large-n quantifier; no induced-universality refinement is claimed. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000868"></a>

### JSP-000868 / Erdős 1046

[Catalog record](catalog-0801-0900.md#JSP-000868) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1046.lean)

- **Recorded scope:** A monic complex polynomial with connected open unit lemniscate has that lemniscate contained in an open disk of radius two.
- **Mathematical credits reported by the source:** Christian Pommerenke.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The monic hypothesis is essential; separate diameter and width questions are not covered. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000870"></a>

### JSP-000870 / Erdős 1050

[Catalog record](catalog-0801-0900.md#JSP-000870) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1050.lean)

- **Recorded scope:** The infinite series over positive n of 1/(2^n-3) is irrational.
- **Mathematical credits reported by the source:** Peter B. Borwein.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The n=1 negative term is included; no general Lambert-series/transcendence claim. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000884"></a>

### JSP-000884 / Erdős 1064

[Catalog record](catalog-0801-0900.md#JSP-000884) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1064.lean)

- **Recorded scope:** The integers n with phi(n)>phi(n-phi(n)) have density one, while the reverse strict inequality holds infinitely often; a natural-valued o(n) error strengthening is also proved.
- **Mathematical credits reported by the source:** Florian Luca; Carl Pomerance; Grytczuk, Luca and Wotowicz (reverse-infinitude result, as attributed by issue #30).
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The explicit reverse-inequality family alone does not establish density one. Error-function strengthening is natural-valued, not arbitrary real-valued. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/30). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000896"></a>

### JSP-000896 / Erdős 1078

[Catalog record](catalog-0801-0900.md#JSP-000896) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1078.lean)

- **Recorded scope:** Haxell transversal-clique theorem for r equal parts of size n, r>=2,n>0, under the stated strict degree inequality with error 1/(2(r-1)).
- **Mathematical credits reported by the source:** Penny Haxell; Tibor Szabó.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The error tends to zero with r, not with n at fixed r; this is not the later sharp Haxell-Szabo threshold. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000897"></a>

### JSP-000897 / Erdős 1079

[Catalog record](catalog-0801-0900.md#JSP-000897) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1079.lean)

- **Recorded scope:** For r>=4,n>=2, at least ex(n,K_r) edges force a maximum-degree vertex with degree at least n/2 and neighbourhood containing at least ex(d,K_(r-1)) edges.
- **Mathematical credits reported by the source:** Béla Bollobás; Andrew Thomason.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The selected target is the non-strict threshold theorem; a distinct strict strengthening is in the source. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000906"></a>

### JSP-000906 / Erdős 1089

[Catalog record](catalog-0901-1000.md#JSP-000906) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1089.lean)

- **Recorded scope:** For fixed n>=2, the distinct-distance forcing number g_d(n) has asymptotic d^(n-1)/(n-1)! with explicit binomial upper and lower bounds.
- **Mathematical credits reported by the source:** Eiichi Bannai; Etsuko Bannai; Dennis Stanton; Aletheia.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Asymptotic in dimension d for fixed n; no exact formula for every d,n. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000907"></a>

### JSP-000907 / Erdős 1091

[Catalog record](catalog-0901-1000.md#JSP-000907) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1091.lean)

- **Recorded scope:** erdos_1091_resolution and erdos_1091: every finite four-chromatic K₄-free graph has an odd cycle with at least two chords, while no unbounded local-colorability-based chord guarantee exists. Explicit four-critical counterexamples have 20m+31 vertices and at most ten chords per cycle.
- **Mathematical credits reported by the source:** Voss; Boris Alexeev; Matthew Putterman; Mehtaab Sawhney; Mark Sellke; Gregory Valiant.
- **Formalization credits reported by the source:** OpenAI Codex.
- **Attribution qualification:** This main file has Authors: OpenAI Codex rather than a Formal authors block; the mathematical names are preserved from its introduction (Voss and the APSSV team). It is published by third-party plby, not the official OpenAI account.
- **Limits and review status:** Not independently recompiled during this catalog audit. Main exported statements and actual proof endpoints read; Voss case modules and all transitive imports not independently replayed. The K₄-free condition is material.

<a id="jsp-000912"></a>

### JSP-000912 / Erdős 1099

[Catalog record](catalog-0901-1000.md#JSP-000912) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1099.lean)

- **Recorded scope:** For each alpha>1, the sum of alpha-th powers of consecutive relative divisor gaps has bounded liminf, witnessed by a cofinal sequence.
- **Mathematical credits reported by the source:** Michael D. Vose.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Bounded liminf only; factorial, lcm witnesses and alpha=1 logarithmic variant are not covered. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000925"></a>

### JSP-000925 / Erdős 1114

[Catalog record](catalog-0901-1000.md#JSP-000925) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1114.lean)

- **Recorded scope:** For N>0 and a nonzero polynomial of degree N+1 with equally spaced roots indexed 0,...,N and positive spacing, derivative-root gaps are symmetric and nondecreasing from the midpoint to the right.
- **Mathematical credits reported by the source:** Elemér Bálint.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Uses corrected degree/root indexing and assumes the derivative-root selector in the open root intervals; that selector is not constructed by this target. Inequalities are non-strict. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000945"></a>

### JSP-000945 / Erdős 1140

[Catalog record](catalog-0901-1000.md#JSP-000945) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1140.lean)

- **Recorded scope:** not_erdos_1140: only finitely many positive n have n−2x² prime for every natural x with 2x²<n (including x=0).
- **Mathematical credits reported by the source:** Mihai Epure; Alexandru Gica; Richard A. Mollin; Hugh C. Williams.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol; GPT-5.4 Pro (retained original Authors header).
- **Attribution qualification:** Current Formal authors block lists Codex and GPT-5.6 Sol; retained original header also names GPT-5.4 Pro and copyright Boris Alexeev. Preserve both provenance layers.
- **Limits and review status:** Not independently recompiled during this catalog audit. Read main, Base, and Analytic proof files; Burgess/Siegel dependency closure not independently audited. Does not claim exact classification. The JSP title omits the original infinitude quantifier.

<a id="jsp-000985"></a>

### JSP-000985 / Erdős 1180

[Catalog record](catalog-0901-1000.md#JSP-000985) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1180.lean)

- **Recorded scope:** For each epsilon>0, a bounded number of sums of inverses of admissible positive integers n<=p^epsilon covers every residue for every prime p.
- **Mathematical credits reported by the source:** A. A. Glibichuk.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** No optimal dependence on epsilon; noninvertible denominators excluded. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-000990"></a>

### JSP-000990 / Erdős 1185

[Catalog record](catalog-0901-1000.md#JSP-000990) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1185.lean)

- **Recorded scope:** The uniform arithmetic-progression assertion is false already for density 1/200 and progression length three, with counterexamples beyond every threshold.
- **Mathematical credits reported by the source:** Hillel Furstenberg.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Disproof of the stated uniform assertion, not all possible density/difference-set refinements. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-001000"></a>

### JSP-001000 / Erdős 1195

[Catalog record](catalog-0901-1000.md#JSP-001000) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1195.lean)

- **Recorded scope:** The integral of F(x)/x^2 on [1,infinity) is finite exactly when the required infinite-measure set with no integral ratios can eventually dominate the nonnegative monotone divergent growth F.
- **Mathematical credits reported by the source:** Boon Suan Ho; GPT-5.4 Pro.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The growth lower bound is eventual, not required for every x>=1. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-001003"></a>

### JSP-001003 / Erdős 1198

[Catalog record](catalog-1001-1022.md#JSP-001003) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1198.lean)

- **Recorded scope:** A two-coloring of positive integers forbids the requested monochromatic nontrivial sums of products on every infinite increasing sequence.
- **Mathematical credits reported by the source:** Gregory L. Smith.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The excluded trivial expression is one single-element block; other admissible sums of products are included. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-001010"></a>

### JSP-001010 / Erdős 1205

[Catalog record](catalog-1001-1022.md#JSP-001010) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1205.lean)

- **Recorded scope:** The optimal common covering multiplicity using one residue class modulo each n<=x is asymptotic to log x.
- **Mathematical credits reported by the source:** Thomas Bloom.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** No sharper secondary error term claimed. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-001018"></a>

### JSP-001018 / Erdős 1213

[Catalog record](catalog-1001-1022.md#JSP-001018) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1213.lean)

- **Recorded scope:** Each positive starting value and gap bound admits a terminal-value bound beyond which an increasing finite sequence has two distinct nonempty consecutive blocks of equal sum.
- **Mathematical credits reported by the source:** Norbert Hegyvári.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** Existence of a bound only, not optimal dependence on the gap bound. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-001020"></a>

### JSP-001020 / Erdős 1215

[Catalog record](catalog-1001-1022.md#JSP-001020) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1215.lean)

- **Recorded scope:** There is no uniform escape-path length bound for positive-degree complex polynomials equal to one at zero and with all roots on the unit circle.
- **Mathematical credits reported by the source:** Gerald R. Mac Lane.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Attribution qualification:** Exact Informal authors / Formal authors header of pinned source; plby is repository publisher, not inferred proof author.
- **Limits and review status:** The initial path point must be exempt from strict modulus <1 since P(0)=1; path length is total variation. This catalog audit did not recompile the proof; the linked issue reports successful compilation, axiom checks and Lean-kernel replay, and leaves committee verification pending.
- **Existing evidence registration:** [Review thread](https://github.com/TheJustinSunPrize/awards/issues/24). The report is credited to its original poster; it is not a replay performed for this correction.

<a id="jsp-001021"></a>

### JSP-001021 / Erdős 1216

[Catalog record](catalog-1001-1022.md#JSP-001021) · [Pinned Lean source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1216.lean)

- **Recorded scope:** f_fourteen_eq_five proves f(14)=5, and not_erdos_1216 refutes the conjectured formula f(n)=floor(log₂n)+1; includes every 14-vertex tournament, not just one witness.
- **Mathematical credits reported by the source:** K. B. Reid; E. T. Parker.
- **Formalization credits reported by the source:** Codex; GPT-5.6 Sol.
- **Limits and review status:** Not independently recompiled during this catalog audit. Main module read; approximately 3.26 MB certificate module not fully read or independently replayed. This does not claim exact f(n) for every n.
