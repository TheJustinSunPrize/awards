# Draft: JSP-000780 — Cohn's all-noncube strengthening

Prepared submission text. Publication status and immutable evidence references belong to the accompanying pull request.

This formalizes the known Cohn strengthening of the 3-powerful triples result:
there are infinitely many positive natural-number triples (a,b,c) with a+b=c,
all three pairs coprime, all three entries 3-powerful, and each entry separately
not a perfect cube. The final theorem has no seed, recurrence, or growth
hypotheses left for the caller to prove.

The base recurrence is adapted with the Apache-2.0 attribution from inoader's
PR #65, commit b5b70857b2d77d6a060e00956beb8e19918b48f9. That submission explicitly
excludes the all-noncube strengthening. The only port adjustment to its proof
is a `norm_num` step for the original seed under Lean 4.33.1. New work proves
that multiplication by a positive cube preserves being a noncube, certifies
Cohn's new seed, preserves the strengthened invariant, and derives infinitude.

The seed was checked against page 439 of J. H. E. Cohn, A conjecture of Erdős
on 3-powerful numbers, Math. Comp. 67 (1998), 439–440,
https://doi.org/10.1090/S0025-5718-98-00881-3 . The readable source is the Leiden
mathematics mirror linked in the package README. All arithmetic properties are
proved in Lean; the Python preflight is not a proof assumption.

Final verification run: 0dcac7b76bd84c479fe61297eefafbe1, PASS, exit 0. Three
project modules were recompiled with warnings treated as errors. Six axiom
reports contain only allowed standard axioms. Actual negative fixtures,
same-kernel `leanchecker --fresh`, and six verifier regression tests passed.
Eight checked source/configuration hashes are recorded in logs/results.json.
Lean 4.33.1 and all nine dependencies are pinned. Official dependency caches
were used; no second kernel implementation was run. Shared logs are explicitly
labeled path-redacted copies, with originals retained locally.

The package does not claim new mathematics, global formalization priority,
or a solution to the other higher-power variants of Erdős 939. Review of the
specified sources found no complete equivalent all-noncube formalization;
the search limits are disclosed in SCOPE_AND_PRIOR_ART.md.

The complete source and redacted evidence are included in the proposed awards
submission directory. Official repository validation, links, build, data check,
history checks, and all 22 tests passed on the complete local change. These
structural checks do not verify the mathematics. Default whole-diff whitespace
checks reported retained evidence line endings; source and documentation checks
with CRLF recognized passed. Original failed diagnostics remain disclosed.

Permanent archival, any operator-designated independent verification, eligibility,
and an award decision remain pending. No recipient nomination, allocation,
global-priority claim, or payment entitlement is asserted. Source and release
references are supplied in the actual pull request; no pending check is marked
as an official success.
