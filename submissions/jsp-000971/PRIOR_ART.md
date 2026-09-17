# Prior work and claim limits

An existing formalization of the same mathematical conclusion predates this submission:

- Repository: https://github.com/plby/lean-proofs
- Integration source: https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1166.lean
- Core: https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1166/Erdos1166Core.lean
- The integration file's history includes commit `1af5b88f430ff5a7800d8691e493d43c97eab963`, dated 2026-08-23, with message `Add Erdos1166.`; a later lint commit is `be7867316ade0e558d6d33e63a0f1377b2298834`.
- The pinned integration source has Git blob `682558eae0a0e4d0e269a6e9c672cd7ac82118cb`.

The public integration declares `Erdos1166.erdos_1166` without an unproved HLOZ parameter. Its core defines the cumulative favorite bound with a positive real constant and an eventual bound by log squared; the integration discharges the eventual-three-sites input using the completed Problem 1165 development. Its maximum-local-time route uses return probabilities, Kac moments and a dyadic tail argument. We inspected these statements and their source history; this submission does not certify a separate clean compilation of that existing 1166 development.

Our alternative implementation uses the same upstream 1165 probability law and eventual-three-sites result, a separate finite-set counting implementation, and a maximum-tail route through fixed-origin return tails and a first-visit shift cover. This is a different implementation of the established conclusion, not a claim of first formalization, first mathematical solution, exclusive credit or a guaranteed award allocation.

At pre-submission inspection, the official JSP-000971 catalog still recorded `Lean proof: No` and `Eligible to claim: No`. Those screening fields do not override the prior source evidence and are not changed by this submission. No matching official issue/PR was returned by searches for the exact ID or `1166`; this limited search is not proof that no earlier submission or private review exists.

The Prize Operator must decide admissibility, attribution, priority and any allocation. Local Lean verification and this contribution's public timestamp do not settle those questions.
