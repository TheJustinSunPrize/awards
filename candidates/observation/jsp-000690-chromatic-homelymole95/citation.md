# Citation

Preliminary public observation candidate, under verification. This record does not announce an award or establish a formal verification result.

## English

JSP-000690 asks whether a three-uniform, critically three-chromatic hypergraph can have minimum degree at least seven. Ruiliang Li's [2025 paper](https://arxiv.org/abs/2512.24850v1) provides the mathematical construction for the chromatic interpretation: a nine-vertex, 22-edge hypergraph with minimum degree seven, chromatic number three, and two-colourability after deletion of any single edge or vertex. Mathematical discovery credit belongs to Li.

The proposed contribution recorded here is a Lean 4/Mathlib formalization of that chromatic result, available in the [public proof repository](https://github.com/homelymole95/jsp-000690-chromatic-lean) at commit [`4dc3c7ebce6bb7fbdff6575c14a77c1e068d18e5`](https://github.com/homelymole95/jsp-000690-chromatic-lean/commit/4dc3c7ebce6bb7fbdff6575c14a77c1e068d18e5). Its top-level theorem is `Jsp000690.jsp000690 : Jsp000690.JSP000690Statement`, with Lean `v4.35.0-rc2` and Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The pinned repository contains its build instructions and audit evidence. This observation record does not treat the repository's own audit as an official independent prize verification.

[Correction issue #697](https://github.com/TheJustinSunPrize/awards/issues/697) requests review of the problem-bank Lean evidence; [recipient recommendation #704](https://github.com/TheJustinSunPrize/awards/issues/704) concerns the Lean formalization contribution, with recipient confirmation pending. [Issue #126](https://github.com/TheJustinSunPrize/awards/issues/126) presents a parallel, same-scope chromatic formalization and recipient recommendation. These submissions should be evaluated on their own pinned evidence; this record asserts no exclusive priority or determination of recipient attribution. The separate transversal interpretation is outside this candidate's proof scope.

The formal statement, official independent verification, recipient confirmation, and any award decision remain pending. Accordingly `verification.formal` is null and `verification/record.yaml` contains null.
