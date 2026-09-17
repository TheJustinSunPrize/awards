# Submission repository checks — 2026-09-17

Base: `TheJustinSunPrize/awards` commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`.

The following organizer-provided checks completed successfully in the
submission working tree, using a Python environment with the repository's
required validation dependencies:

```text
python scripts/manage.py validate
validate: OK
python scripts/manage.py links
links: OK
python scripts/manage.py build
build: OK
python scripts/manage.py check
check: OK
python scripts/manage.py history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae
history: OK
python -m unittest discover -s tests -v
Ran 22 tests
OK
```

The commands above are the observed invocations with the environment's
absolute Python path shortened to `python`; this is a summary, not a raw
terminal transcript. No validator code or tests were modified. Generated
data indexes have no changes. The submission only adds its own directory
under `docs/submissions/`.

Nine proof, audit, toolchain, lockfile and reproduction files were compared
byte-for-byte against the published, tested proof tree. Their exact byte
counts and SHA-256 values are recorded in
`verification/submission-source-manifest.json`.

These structural checks do not establish mathematical novelty, statement
fidelity or award eligibility. Mathematical checking and its limitations
are described separately in `VERIFICATION.md`.
