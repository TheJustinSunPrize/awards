# Local verification evidence

Run `e1b7f288-c970-4f32-b09a-cd8f52f900cc` started at `2026-09-16T20:16:29.491332+00:00`. Both final theorem closures
passed. This is applicant-provided reproducible evidence, not organizer acceptance.

| Stage | Exit code | Seconds |
|---|---:|---:|
| compile-KorskyDefs | 0 | 41.156 |
| compile-KorskyCount | 0 | 37.49 |
| compile-KorskyInject | 0 | 49.165 |
| compile-KorskyModular | 0 | 46.507 |
| compile-Erdos882Original | 0 | 31.19 |
| compile-KorskyEndpoint | 0 | 28.578 |
| compile-Erdos882Korsky | 0 | 22.985 |
| leanchecker | 0 | 233.687 |
| export | 0 | 25.185 |
| nanoda | 0 | 1.337 |

Nanoda checked **7691 declarations with no errors** and printed the two named
final statements. Its permitted axioms were exactly `propext`, `Classical.choice`,
and `Quot.sound`; unpermitted axioms and unknown target declarations were hard
errors. Lean's axiom reports show the same three standard axioms.

See [verification.json](verification.json), [check-logs.txt](check-logs.txt),
[TOOL_PROVENANCE.json](TOOL_PROVENANCE.json), and [nanoda.json](nanoda.json).
The portable Nanoda configuration is run from the package root after placing
the export at `verification/proof.ndjson`.

## Export identity and publication status

- Export size: 30509530 bytes.
- Export SHA-256: `5e46bd13762e25b67eb19caacee0756b18364ab8d7c67478c93ed750bcae21cb`.
- Exact main source SHA-256: `d1a4946b8147a0f336710cb91a21b75772169c4b5595945abb476ecd208738d5`.
- Full export is included in the prepared verification attachment.
- A public fixed-version release and permanent external archival have not yet
  been confirmed at the time this attachment was assembled. The final PR and
  its artifact-publication record must state the actual publication status.

## Limits and additional checks

All seven local modules were freshly compiled. Check commands ran with network
access denied; an accessible control and a denied-network probe were both
recorded. The filesystem was not isolated. Pinned dependency objects were
reused, not rebuilt from source. Exporter and Nanoda binaries were reused with
the recorded provenance and verified hashes.

[negative-controls.json](negative-controls.json) records a prior successful
standalone check of the identical negative-control source and identical four
core modules. Dropping NoDouble makes the sum bound false for weights (1,2);
dropping Ordered permits a collision with weights (4,6,7). Those checks do not
replace the final theorem verification.

[prior-submissions.json](prior-submissions.json) records a bounded public
duplicate search. Statement fidelity is discussed in the source-scope review.
Designated offline review, archive acceptance, PR merge, priority, award tier,
recipient confirmation and payment remain organizer decisions.
