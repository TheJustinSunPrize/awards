# Evidence redaction

Files in `logs/`, `development/`, and the source-check evidence are explicitly
labeled redacted copies, not untouched raw output. Originals remain locally.

Only local path prefixes are replaced: the project directory by `<PROJECT_ROOT>`,
the toolchain directory by `<LEAN_TOOLCHAIN>`, the workspace by `<WORKSPACE>`,
and the user directory by `<USER_HOME>`. Windows, slash-separated, and JSON
escaped spellings are handled. Exit codes, run states, actual failures,
declaration names, axiom lists, and source hashes are preserved. Text is UTF-8.

`evidence/redaction-map.json` records original and copy SHA-256 hashes.
Source, dependency locks, toolchain configuration, verifier, and regression
tests were not redacted or translated; all eight still match the final
verification record. Hashes bind bytes and do not constitute independent
certification. `evidence/english-export.json` records the documentation-only
conversion from the Chinese local review package.

Development logs retain the initial port failure and later warnings. Final
success is identified by run `0dcac7b76bd84c479fe61297eefafbe1` in
`logs/results.json`. Official dependency caches were used; there is no claim
to have rebuilt all of mathlib or used a second kernel implementation.
