# Submission package — JSP-000070 (Erdős problem 42)

Status: **pending-recipient-confirmation** · prepared 2026-09-17 (tick17)

## Claim summary

Erdős problem #42 (https://www.erdosproblems.com/42): for any integer set with
distinct two-element sums, does another such set always exist with no common
nonzero differences? — answered (solution + Lean 4 formalization).

## Pinned commits

| Artifact | Commit / version |
|---|---|
| Upstream repo (proof source) | https://github.com/plby/lean-proofs @ `1268917deaaaa0d674f651287027baa26cea9920` |
| Formalization file | `src/latest/ErdosProblems/Erdos42.lean` (same pinned commit) |
| Current-release re-verification | mathlib @ `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0), Lean `leanprover/lean4:v4.34.0` |
| v4.34-adapted source (this repo) | commit `49d4007` (candidates/verified-pending/jsp-000070 + verify-current/Erdos42.lean) |
| Source SHA-256 | `749BC7F780F5673A6D18A0C76778951C8A5858046D462CEF36C98D87980A5446` |

## PR body (draft, to upstream repo)

> **Formal proof of Erdős problem 42 (Sidon-type two-element sums) in Lean 4**
>
> This pull request makes the Lean 4 formalization of Erdős problem 42
> available for review. The pinned upstream commit `1268917d` contains the
> self-contained file `Erdos42.lean` (compact-Cayley / Fourier-analytic route;
> math proof by Harjas Sandhu, formalization by Pawan Sasanka Ammanamanchi).
>
> The file has been independently re-verified against the current release
> (Lean v4.34.0, mathlib v4.34.0 @ `5ed29652`) by an automated verifier
> (`jsp070-verifier`); the only adaptation was mechanical: 15 call sites of
> `Finset.prod_le_one`/`prod_le_prod` rewritten to the v4.34
> `prod_le_one₀`/`prod_le_prod₀` API (explicit non-negativity hypotheses, no
> mathematical change). Build green; `#print axioms` for
> `compact_cayley_clique` (and the four further entry points) reports exactly
> `[propext, Classical.choice, Quot.sound]`.
>
> Recipient placeholder: **RECIPIENT-JSP-000070-A** (identity confirmation
> pending per prize rules).
>
> Verification evidence: `candidates/verified-pending/jsp-000070/` in the
> companion records repository (this repo) — `award.yaml`, `citation.md`,
> `recipients.md`, `verification/record.yaml`, `verification/statement.yaml`
> (active statement `STMT-jsp-000070-v2`), `verification/current-release-v4.34.log`,
> `verification/independent-verification.md`. `python scripts/manage.py validate`
> passes.

## Submission checklist

- [x] Upstream pinned commit identified and cloned
- [x] Current-release (v4.34.0) re-verification green (build + axioms)
- [x] Four-piece record set complete and schema-validated (`validate: OK`)
- [x] Statement v2 active (mathlib v4.34.0 pinned), v1 retained as superseded
- [x] Sandbox attestation documented (non-elevated token; offline verification;
      source-built mathlib)
- [x] Recipient placeholder `RECIPIENT-JSP-000070-A` in place
- [ ] Recipient identity confirmation (human step, pending)
- [ ] Public award announcement in `awards/` (human step, after confirmation)
- [ ] Final report (`state/final-report.md`)
