# Actual local verification evidence

This is an unsigned local evidence summary, not a completed formal review
record and not an issued statement.

| Item | Actual result |
| --- | --- |
| Lean version | 4.34.0, ARM64 macOS, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. |
| Full official distribution archive | 561666156 bytes; SHA-256 `69f263fa6e21bbc2466bbfb1affcd92479ee2714c883a07de548e099a5922932`, matched the official asset digest. |
| Source SHA-256 | `8849a0a8c2295e852c3ef5203a2b112b70a7d019471971bc9b4c75efc97b265a`. |
| Source compilation | Exit code 0; a fresh `.olean` was produced. |
| Top-level axiom audit | Both `JSP000301.counterexample` and `JSP000301.original_claim_false`: `[propext, Quot.sound]`. |
| Same-toolchain replay | `leanchecker --verbose Counterexample`, exit code 0. Not an independent verifier. |
| Arithmetic cross-check | The companion Python script independently factors 12167 and 12168 and checks exact integer square roots; it passed. |
| Statement comparison | Authoring-session comparison supplied in the statement draft and proof guide; unsigned and not independently reviewed. |
| Public source and artifacts | Published branch revisions supply source and logs; the intake issue pins an immutable commit. No scholarly archive or priority claim is asserted. |
| Independent review, signatories, approval | None obtained; pending. |
| Required safe-version and isolation approval | Not established. Official distribution and bundled library artifacts were used. Network isolation was not asserted by the runner, and no memory cap was set. |

Actual outputs:

- [Lean build and axiom output](../evidence/lean-build.log)
- [Build metadata and hashes](../evidence/lean-build.json)
- [Kernel replay output](../evidence/leanchecker.log)
- [Exact arithmetic check](../evidence/arithmetic-check.log)
- [First attempt timeout](../evidence/lean-attempt-1-timeout.log)
- [Second attempt stopped](../evidence/lean-attempt-2-stopped.log)
- [Failed intermediate elaboration](../evidence/lean-attempt-3-error.log)

Only `lean-build.log` and `lean-build.json` describe the final successful
source. Earlier attempt files are retained transparently, not accepted as
proof evidence. Repository checks for the publication revision are summarized in the packet README and PR.
This documentation packet is outside the live records; it does not claim to
satisfy the requirements for a completed award or formal verification record.
