# JSP-000307 Lean 4 submission (lyssom)

## Contents

- `JSP000307.lean` — the formalization (Lean v4.33.0 + Mathlib v4.33.0)
- `README.md` — toolchain, build, axiom audit details
- `build.log` — full `lake build JSP000307` output plus axiom audit
- `lean-toolchain`, `lakefile.toml` — toolchain pinning

## Theorem

```lean
theorem JSP_307 :
    ∃ n : ℕ, IsLPF n 13 ∧ IsLPF (n + 1) 7 ∧ IsLPF (n + 2) 5
      ∧ 13 > 7 ∧ 7 > 5
```

Witness: `n = 13`. 13, 14, 15 have largest prime factors 13, 7, 5.

## Axiom audit

Every proved theorem depends only on:

- `propext`
- `Classical.choice`
- `Quot.sound`

No `sorry`, `admit`, custom mathematical axioms, or `native_decide`
trust oracle.

## Reproduction

```bash
lake build JSP000307    # 8707 jobs total
```

## Authorship

- Lean 4 / Mathlib author: lyssom (with AI assistance from MiniMax-M3)
- Mathematical credit: Erdős–Pomerance (1978) [ErPo78], Balog (2001) [Ba01]
- Public release: https://github.com/lyssom/jsp-000307-lean
- Related upstream record: https://github.com/TheJustinSunPrize/awards/issues/654

## Scope disclosure

This formalization proves the **existence** of a triple (13, 14, 15)
whose largest prime factors are strictly decreasing (13 > 7 > 5). It does
NOT formalize the stronger Balog 2001 result (infinitely many such
triples exist). Tier evaluation should reflect "Partial Progress /
Contribution" rather than full resolution.
