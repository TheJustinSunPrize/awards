# JSP-000907 candidate alternative construction

This note records a **non-claim research submission** related to the second question of JSP-000907 / Erdős Problem 1091.

It does **not** claim first-solution priority, full-scope resolution of JSP-000907, a Lean formalization, or prize eligibility. The second question was already answered negatively in prior work; the contribution linked below is an alternative parameter-uniform construction with a smaller chord bound.

## Claimed mathematical content

For every odd integer `ell >= 3`, the linked note defines a finite graph `G_ell` with the following properties:

- `G_ell` is `K_4`-free and 4-critical;
- every proper subgraph is 2-degenerate and hence 3-colorable;
- every simple cycle has at most 5 chords;
- every odd simple cycle has at most 4 chords;
- the 4-chord odd-cycle and 5-chord all-cycle bounds are both attained within the family.

Consequently, for every positive integer `r`, choosing `ell` with `4*ell+1 > r` gives a 4-chromatic graph whose subgraphs on at most `r` vertices are 3-colorable while every odd cycle has at most four chords. This is an alternative disproof of the second question, not a solution of the entire JSP entry.

## Public proof source

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000907-research-note`
- Pinned commit: `bd9e587d1411903124531f14329d8df98b076692`
- Proof file: https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/bd9e587d1411903124531f14329d8df98b076692/research-notes/jsp-000907/proof.md

The note explicitly states that it is not Lean-verified and that novelty over all prior literature is not established.

## Prior work acknowledged by the proof note

- Alexeev, Putterman, Sawhney, Sellke, and Valiant, *Short proofs in combinatorics, probability and number theory II*, arXiv:2604.06609v1, Section 4.
- Chen and Ning, *Cycle lengths and chords under chromatic and degree constraints*, arXiv:2607.15501v1.
- The Erdős Problem 1091 discussion thread.

This file is intentionally separated from the canonical problem status fields so that maintainers can decide whether the candidate construction warrants any catalog update.
