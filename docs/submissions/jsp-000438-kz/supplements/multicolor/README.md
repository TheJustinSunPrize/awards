# Finite-color supplement to PR #408

This supplements the existing JSP-000438 submission with the known bound

\[
R(T_1,\ldots,T_r)\le 2+\sum_{i=1}^{r}(|T_i|-2)
\]

for every finite nonempty color set and prescribed trees of orders at least
two. The orders need not coincide. This is additional formal integration of
the same credited Erdős–Sós dependency; it is not a separate claim of solving
a new open problem or of mathematical or formalization priority.

## Added contribution

- A general edge-count inequality for finite graph covers of a complete graph,
  allowing overlaps.
- A finite-color tree containment theorem at the stated bound.
- An explicit injective monochromatic vertex embedding for a coloring of
  unordered pairs; all tree edges have the corresponding color.
- A Ramsey-number bound supported by this direct existence theorem, without
  relying on an empty defining set.

The proof assumes no tree-free density result as an unproved hypothesis.
It imports the existing proved `Erdos548.tree_free_edge_bound` and sums it
over the colors. At `N = 2 + sum_i (|T_i|-2)`, avoidance in every color would
give `N(N-1) ≤ (N-2)N`, contradicting `N>0`.

## Source and reproduction

- [Pinned complete proof project, commit 0175b2a7a50f7687ece92f61bbe0e3a2f377913a](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/0175b2a7a50f7687ece92f61bbe0e3a2f377913a/projects/jsp-000438).
- [Exact verification workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/0175b2a7a50f7687ece92f61bbe0e3a2f377913a/.github/workflows/jsp-000438.yml).
- [Public execution 35177218300](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177218300).
- The new module is copied as [Multicolor.lean](Multicolor.lean), with the
  combined [Audit.lean](Audit.lean) and [file hashes](PROOF_SHA256SUMS).

For reproduction, use the **complete pinned project** above, not this excerpt
directory. With its committed Lean 4.34.0 toolchain and lockfile, run
`lake exe cache get`, `bash scripts/verify.sh`, and
`bash scripts/verify_nanoda.sh` from `projects/jsp-000438`.

The original submission's five-target evidence still applies to its original
fixed proof commit. This supplement has its own fixed source and combined
nine-target verification. See the [verification receipt](VERIFICATION.md) for
observed results rather than inferring success from the existence of scripts.

## Attribution and requested review

The substantial extremal theorem is the existing work in
[tadamcz/erdos548 at 82ffb751f3d37768927df9239ed08439bbe0dd09](https://github.com/tadamcz/erdos548/tree/82ffb751f3d37768927df9239ed08439bbe0dd09).
Its original source, Apache-2.0 license and attribution remain in the pinned
project. The new finite-color integration was prepared by the submitting
account `ketianzhang1-lang` with OpenAI Codex assistance. The mathematical
implication is known; no new mathematics or first-formalization priority is
claimed.

This is a self-submission. The proposed recipient remains
`RECIPIENT-JSP-000438-KZ-A`, confirmation pending. Please assess the precise
additional formalization contribution, overlap, attribution, reproducibility
and eligibility together with the original PR. Machine verification does not
constitute human review, organizer acceptance or an award decision.
