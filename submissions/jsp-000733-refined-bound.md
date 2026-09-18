# JSP-000733: refined primitive subset-sum upper bound

For the actual maximum cardinality f(n), this proves f(n) <= log_2(n) + (1/2) log_2(log_2(n)) + 3 for every n >= 32, and the corresponding eventual upper bound. This is a one-sided bound, not an asymptotic equality or a new mathematical discovery.

PR #31 covers the leading asymptotic and excludes this refined error term. The package credits its primitive-to-injective bridge and separately discusses existing generic moment bounds.

The complete reproducible source and evidence are included in this same change:

- [Package instructions](jsp-000733-refined-bound/README.md)
- [Statement and axiom audit](jsp-000733-refined-bound/Audit.lean)
- [Scope and prior work](jsp-000733-refined-bound/SCOPE_AND_PRIOR_ART.md)
- [Recorded verification](jsp-000733-refined-bound/logs/results.json)
- [File hashes](jsp-000733-refined-bound/PACKAGE_SHA256.json)
- [License and attribution](jsp-000733-refined-bound/NOTICE)

Recorded verification run: `4e5e8a02c48f46739006c6dafd238531`, PASS. The package pins Lean 4.33.1
and its dependencies, records fresh project compilation, standard-axiom checks,
actual negative tests and same-kernel fresh replay. Official dependency caches
were used; no second kernel implementation was run. Shared logs are explicitly
labeled path-redacted copies, with original failures and limits preserved.

This submission requests intake and formalization-contribution review. It makes
no claim to an organizer decision, award eligibility, or global priority.
Permanent archival and any official verification remain pending.
