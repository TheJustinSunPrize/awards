# JSP-000780: Cohn's all-noncube strengthening

This proves infinitude of positive natural-number triples (a,b,c) with a+b=c, all three pairs coprime, all entries 3-powerful, and each entry separately not a perfect cube. The theorem has no unproved seed or recurrence hypotheses. Other higher-power variants are outside its scope.

The base recurrence is adapted, with Apache-2.0 attribution, from PR #65 at b5b70857b2d77d6a060e00956beb8e19918b48f9. That submission excludes the all-noncube strengthening. The mathematical result and seed are due to Cohn (1998).

The complete reproducible source and evidence are included in this same change:

- [Package instructions](jsp-000780-cohn-noncube/README.md)
- [Statement and axiom audit](jsp-000780-cohn-noncube/Audit.lean)
- [Scope and prior work](jsp-000780-cohn-noncube/SCOPE_AND_PRIOR_ART.md)
- [Recorded verification](jsp-000780-cohn-noncube/logs/results.json)
- [File hashes](jsp-000780-cohn-noncube/PACKAGE_SHA256.json)
- [License and attribution](jsp-000780-cohn-noncube/NOTICE)

Recorded verification run: `0dcac7b76bd84c479fe61297eefafbe1`, PASS. The package pins Lean 4.33.1
and its dependencies, records fresh project compilation, standard-axiom checks,
actual negative tests and same-kernel fresh replay. Official dependency caches
were used; no second kernel implementation was run. Shared logs are explicitly
labeled path-redacted copies, with original failures and limits preserved.

This submission requests intake and formalization-contribution review. It makes
no claim to an organizer decision, award eligibility, or global priority.
Permanent archival and any official verification remain pending.
