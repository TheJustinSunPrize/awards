# Candidate: JSP-000127 — Erdős problem 119 (polynomial zeros on the unit circle)

This PR adds the **verified-pending** record for **JSP-000127** — Erdős
problem 119 ("If all zeros of a polynomial lie on the unit circle, how does its
maximum modulus on the prescribed region grow with its degree?", historical
bounty $100, catalog status: Solved, Lean proof: Yes, Eligible: Yes,
**Unclaimed**).

## What is verified

Pinned source: [plby/lean-proofs](https://github.com/plby/lean-proofs) @
`1268917deaaaa0d674f651287027baa26cea9920`,
`src/latest/ErdosProblems/Erdos119.lean` (1788 lines, single-file closure:
`import Mathlib` only). Exported declarations verified:

| Declaration | Statement (informal) |
| --- | --- |
| `Erdos119.erdos_119` | ∃ c > 0 (c = 1/256), eventually ∑_{k<n} M z k > n^(1+c) |
| `.parts.iii_quantitative` | eventually C · n^(5/4)/√(log n) < ∑_{k<n} M z k |
| `.parts.ii` | {n \| M z n > n^c} infinite |
| `.parts.i` | limsup_n (M z n) = ∞ |

where `M z n = sSup {‖p z n w‖ \| ‖w‖ = 1}`, `p z n = ∏_{i<n} (w - z i)`.

## Verification method

- **Toolchain**: current release — Lean **v4.34.0**, mathlib **v4.34.0** @
  `5ed2965256430c3649e86755f9576b54eca72435` (source-built, no prebuilt
  artifacts), direct `lean.exe` (no lake env).
- **Compile loop**: exit 0 on entry module and audit module (`Audit127.lean`),
  driver run 2026-09-19 03:26:24 → 03:26:50 (log embedded in
  `verification/current-release-v4.34.log`).
- **Porting**: 2 documented patches for mathlib 4.33 → 4.34 API drift
  (`verification/PORTING-DIFF-127.md`; byte-level diff between
  `hashes-pinned-src.tsv` and `hashes-final.tsv`).
- **Axiom audit** (`#print axioms`): exactly `[propext, Classical.choice,
  Quot.sound]` on all four declarations — no sorryAx, no user axioms, no
  unsafe. Zero `sorry`/`admit` in the 1788-line source.
- **Deps** (`lean --deps`): exit 0 for both modules.

## Attribution (credit only — no authorship claim)

- Informal solution: **ChatGPT 5.6 Pro, Samuel Korsky**
- Statement: **Formal Conjectures authors** (google-deepmind/formal-conjectures
  formalization of Erdős problem 119)
- Formalization: **Codex, Boris Alexeev**
- Public port: **plby** (plby/lean-proofs)
- Recipient (verification credit only): **shiqiang-chen** — per the
  established pattern of PRs #1131/#1171/#1482; files under `people/` are
  required on this branch because `origin/main` does not yet carry any
  `people/` profiles and `manage.py` requires ≥2 curator signatories.

## Checks

- `python scripts/manage.py validate` — pass
- `python scripts/manage.py build` — pass (`data/candidates.json` regenerated)
- Race check before submission: no PRs reference JSP-000127; the only
  [Recipient] issue (#191, Neo7672) was **withdrawn by its author** on
  2026-09-17 (author took no credit and noted the submission should come from
  the repo-controlling account; its cited file `Erdos111.lean` does not exist
  at the pinned commit — the real file is `Erdos119.lean`); catalog still
  marks JSP-000127 **Unclaimed**.
