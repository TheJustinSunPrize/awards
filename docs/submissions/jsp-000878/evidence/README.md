# Reading the evidence

`initial-compilation-receipt.json` consolidates actual successful compilation of all 29 pinned upstream modules. Its source, output and compiler hashes are checked before reuse. Historical failed attempts and the 180-second timeout are retained separately; they are not passing evidence.

`verification.json` is the final fail-closed runner receipt. Its `verified` field must be true before this package is described as locally verified. The independent statement and bridge are always compiled again. The runner requires three final axiom lists containing only standard Lean axioms, replay of the exact 31-module set, and rejection of a false arithmetic statement.

Compiler logs replace only working-directory, Mathlib-directory and toolchain-directory prefixes with `<proof>`, `<mathlib>` and `<toolchain>`. Four trailing spaces in Assembly diagnostic lines were also removed after verification; dependent log and receipt hashes were updated without changing proof sources or compiled outputs. Hashes refer to the published sanitized logs. Successful earlier module outputs were retained across compatibility retries; this is explicitly recorded rather than described as one uninterrupted fresh build.

The replay uses the same Lean toolchain and imported Mathlib. It is not an independent implementation of the kernel, a fresh replay of every Mathlib dependency, or designated independent review. Repository checks validate project structure and links; they do not certify mathematics or prize eligibility.
