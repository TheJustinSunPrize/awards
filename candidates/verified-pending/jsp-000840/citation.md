# Citation

Candidate record for JSP-000840 — Lean formalization of Rademacher's theorem (l = 1 case). This is not an award; verification is under review.

## English

**Status**: candidate, under verification. No award decision is claimed.

**Result formalized.** Every graph on `n ≥ 3` vertices with at least `⌊n²/4⌋ + 1` edges contains at least `⌊n/2⌋` triangles (Rademacher, 1962). The proof was formalized in Lean 4 (v4.33.0, mathlib `db584cd6`) as `Rad.rademacher` in the public repository https://github.com/aichiwuhuarou/rademacher-lean, first pushed 2026-09-17T14:42Z. The formalization is a strong induction on the vertex count using mathlib's Turán machinery for Mantel's theorem, handshake-lemma degree arguments, vertex deletion, and a degree-excess pigeonhole; full details are in the repository's README and PROOF.md.

**Scope.** The catalogued entry records the general answer of Khadzhiivanov–Nikiforov (1981): `⌊n²/4⌋ + l` edges force at least `⌊n/2⌋ · l` triangles for `2l < n`. This candidate formalizes the `l = 1` case only. The general case requires the long structural proof of Lovász–Simonovits and is not included; accordingly this candidate is submitted as partial coverage of the entry, not as a completed formalization of the general theorem.

**Evidence.** The repository builds locally (`lake build`, all targets) and independently on GitHub Actions (`leanprover/lean-action@v1`, run `35235416616`, 15m26s, passed; log archived as a commit-pinned blob inside the repository). The axiom audit reports only `[propext, Classical.choice, Quot.sound]`, reproducible with the repository's `Audit.lean`. A prior-art search on 2026-09-17 found no existing Lean formalization of this theorem (statement or proof) anywhere.

**Attribution.** The theorem is due to E. Rademacher (1962, unpublished). The formalization was produced with AI assistance (GLM, via the ZCode agent) under the direction of the declarant `aichiwuhuarou`, a natural person; all Lean scripts are original to the repository. Recipient confirmation and identity verification remain pending, so recipients are listed under a placeholder in `recipients.md`.

A registration application for the same formalization was previously filed as issue #792; this candidate record is the formal channel counterpart referenced there.
