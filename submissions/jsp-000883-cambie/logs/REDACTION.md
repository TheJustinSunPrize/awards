# Public evidence copies

All `.log` files in this directory are explicitly labeled public copies, not
unmodified raw output. JSON records that required redaction, and `results.json`,
contain a `_public_copy` disclosure. Unmodified originals remain in the local
verification package or its private history; they are not included in this export.

## Replacement rules

Only known environment paths in log and evidence records were replaced. Matching
is case-insensitive, accepts forward or backward separators (including escaped
backslashes), and applies the longest known prefix first:

| Token | Meaning |
| --- | --- |
| `<PROJECT>` | Local audited proof-project directory |
| `<WORKSPACE>` | Local task workspace directory |
| `<LEAN_BIN>` | Pinned Lean toolchain executable directory |
| `<PYTHON>` | Python interpreter executable used by the verifier |
| `<USER_HOME>` | Local user's home directory |

Private prefix values are deliberately absent. Relative suffixes, command
arguments, timestamps, failures, exit codes, theorem names, axiom reports, and
verification limitations are retained. Public copies are encoded as UTF-8. Logs
gain a disclosure header; JSON records with disclosures are serialized with
two-space indentation and a final newline. These presentation changes are also
reflected in their hashes, including when the replacement count is zero.

`redaction-manifest.json` records original/public byte counts and SHA-256 hashes,
record roles, and replacement counts by token. This establishes internal
traceability; hashes and public copies are not independent certification.
The eight source/configuration hashes in `results.json` are unchanged and match
the published source bytes. Source code, toolchain configuration, dependency
lockfile, licenses, and public reference source snapshots were not redacted.

## Distinct record roles

- Top-level verification logs and `results.json` refer to the final recorded Lean
  verification run, identified by the run ID in `results.json`.
- `setup/dependency-cache*.log` are original dependency setup attempts from before
  the final run. They retain the original failure and retry output and are not
  evidence of a new clean dependency build.
- `verifier-tests.log` records Python lifecycle regression tests. It does not
  claim to compile Lean or rerun the Lean negative fixtures.
- `evidence/` retains preparation records and public-source reference evidence;
  it is not part of the compiled proof modules.

The final verification used the official dependency cache. It did not rebuild
all of Mathlib, run a second kernel implementation, or obtain official prize
verification. The `leanchecker --fresh` replay uses the same Lean kernel, with
the tool's documented treatment of unsafe and partial declarations.
