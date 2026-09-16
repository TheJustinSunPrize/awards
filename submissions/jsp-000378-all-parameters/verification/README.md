# Observed verification results — 2026-09-16

All four recorded commands exited zero: Lean compilation, `leanchecker --fresh`, theorem-closure export, and Nanoda. Nanoda checked **27,805 declarations with no errors**. Both target theorem types and the three admitted axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in its complete log.

The canonical source SHA-256 is `1e4c3c35392b21578cf3f620b56dc3dee6f0db3c3040d9b1afca92a2d0c2a20a`. Its bytes remained unchanged throughout verification.

The exported theorem closure is 145,728,907 bytes with SHA-256 `35fc58ff0e23fa84afd99f6086b39a096879d3affdcc85116b6f58faedec8ec4`. This large generated file is retained locally and is not bundled or committed; reproduce it using the pinned exporter and instructions in `../verification-tools/VERIFY.md`. `nanoda.reproduction.json` is a portable copy of the actual configuration with only its export path changed.

`verification.public.json` is the machine-readable execution record with local path placeholders. `LOG_PUBLICATION.json` records original and published log hashes; private filesystem paths were replaced, and originally empty logs are represented by a single newline added by the GitHub web editor. This serialization is explicitly recorded in the hash map; it does not add checker output. The exit status for every command is in the execution record.

The checking commands had network access disabled, verified by a control probe. They used cached dependencies and did not run in a filesystem sandbox or rebuild all dependencies from source. Leanchecker uses Lean's kernel; Nanoda is the independently implemented Rust kernel. Official statement review, eligibility and award decisions remain pending.
