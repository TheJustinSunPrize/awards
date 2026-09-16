# Verification record copies

All logs in this directory are explicitly marked path-redacted copies, not unmodified raw output. Originals remain in the local work directories. JSON `_public_copy` metadata and `redaction-manifest.json` record original/copy hashes and replacement counts. Hashes establish byte correspondence, not independent execution or certification.

Only known environment paths are replaced, using longer prefixes first and accepting either slash style and JSON escaping: `<PROJECT>` is the English verification directory; `<PRIOR_PROJECT>` is the earlier Chinese development directory; `<WORKSPACE>` is the local task workspace; `<LEAN_BIN>` is the Lean binary directory; `<PYTHON>` is the Python executable; `<USER_HOME>` is the user directory. Genuine output, failures, states, exit codes, and verification limits are retained. A copy header or JSON metadata is added.

Top-level command logs and `results.json` record the final run on the English source bytes. `preparation/` contains earlier development output, including unsuccessful attempts. Those earlier records are not bound to the translated final bytes and do not claim to cover the entire development history. `verifier-tests.log` covers Python regression tests only.

The final verifier recompiles all seven project modules and uses official dependency caches. It does not rebuild all mathlib dependencies. `leanchecker --fresh` replays through the same Lean kernel, not a second implementation, and is not organizer acceptance. No remote publication was performed.
