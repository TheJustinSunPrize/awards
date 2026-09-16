# Attribution and contribution boundaries

Noga Alon is the author of the mathematics: [*Blocking partial designs and block-compatible sequences*](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf), Theorem 2.3. Erdős posed the counting problem. This package contributes additional formalization and does not claim the construction, its mathematical proof, or its binomial counting formula as new discoveries.

The dependency is `ErdosProblems.Erdos732` from [plby/lean-proofs at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos732.lean). Its header credits Codex and GPT-5.6 Sol as formal authors, Noga Alon as informal author, and carries the Formal Conjectures Authors' Apache 2.0 notice. The upstream file is imported unchanged. Its SHA-256 is `752d9a781a713dd96e55b482e584ccc4227cb2b698795f6c0cd474d18945db34`.

The additional work was prepared with Codex assistance:

- `FinitePlane.lean` explicitly adapts the upstream projective-plane geometry from `ZMod q` to arbitrary finite fields. The original provenance and notices are retained.
- `Profiles.lean` adapts the upstream truncation argument to arbitrary profiles, reindexes lines to handle arbitrary universes, and derives the explicit completion formula. Existing completion-by-pairs, pair-count and size-bound lemmas are reused rather than claimed as new work.
- `Counting.lean` counts unrestricted profiles using Mathlib's symmetric powers and stars-and-bars theorem, then proves the constructed family has that cardinality through profile recovery.
- `PrimePowers.lean` specializes the new construction to Mathlib's `GaloisField p k` and records the order-four and order-five examples. The finite-field existence and cardinality results themselves belong to Mathlib.

Mathlib supplies the underlying projectivization, incidence geometry, finite-field and multiset infrastructure. The development baseline is [mathlib4 commit `db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d), with Lean 4.33.0. Existing library authorship and licensing remain in force.

[PR78](https://github.com/TheJustinSunPrize/awards/pull/78), inspected at head `bb4c53e847da438895921ee2290ca19437e08996` in `CollinYuanjieRen/awards`, formalizes an upper bound. Its `Design`, `LargeBlocks`, `Encoding`, and `Main` modules were reviewed for overlap. They are prior art, not imported dependencies of this candidate, and their upper-bound contribution is not claimed here.

The four contribution Lean modules are released under the Apache License, Version 2.0, supplied in `LICENSE-APACHE`. The adapted geometry and construction retain the upstream notice: "Copyright 2026 The Formal Conjectures Authors." The modifications and their provenance are described above and in the source headers. The Python helper follows this repository's MIT code license; documentation follows its content license. No dependency license is replaced by these statements.

The submission category is **Partial Progress**. Neither the existing lower bound nor PR78's upper bound is presented as this package's new contribution. Recipient identity, official recognition, eligibility and award allocation are outside this contribution.
