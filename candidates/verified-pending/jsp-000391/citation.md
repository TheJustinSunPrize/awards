# Candidate citation: 000391

## English

Floor recurrence generating digits of an algebraic number (Graham-Pollak) (catalog 000391; [GrPo70] Note on a nonlinear recurrence related to sqrt 2 (1970); [St05] J. Integer Seq. 2005).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `e8872b9b405206ce100f5131a9ce744a6f0c9d32`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems Jsp391.d_mem_zero_one, Jsp391.step_step_digit, Jsp391.u_strict_mono are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

Complete Lean 4 formalization of the Graham-Pollak digit phenomenon: d_n = u_{2n+1}-2*u_{2n-1} in {0,1} (binary digits of sqrt 2), with full proof chain, 0 sorry/admit. scoped to the core digit-binary claim.

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
