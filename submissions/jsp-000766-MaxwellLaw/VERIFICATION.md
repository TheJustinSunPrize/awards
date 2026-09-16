# Verification record

Final end-to-end verification completed at **2026-09-16T16:59:06.024498+00:00** (UTC).

## Statement correspondence

[Audit.lean](Audit.lean) prints the actual exported types in [axioms.log](evidence/axioms.log). `Jsp000766.erdos_922` and `Jsp000766.erdos_922_colorable` quantify over an arbitrary vertex type, a simple graph, and every natural number `k`. They have the explicit finite-set hypothesis and conclude the chromatic bound and existence of a coloring by `Fin (k + 2)`.

There is no vertex-finiteness, countability, nonemptiness, local-finiteness, or decidability assumption. In particular `k = 0` is covered. `finite_subgraphs_iff_finsets` proves equivalence with the condition on all subgraphs having a finite vertex set, including subgraphs obtained by deleting edges. `erdos_922_of_finite_subgraphs` gives the result from that formulation.

## Observed results

- Lean `4.33.0`, release commit `d8b18978322de05a8f3dba51ef03cf5461676c17`; pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- The unchanged 233,944-byte finite proof passed its pinned SHA-256 check and was compiled locally from source.
- Source fetching also succeeded from a previously empty directory, without GitHub authentication.
- The entire package built successfully, including the general theorem and both hypothesis formulations.
- All seven audited declarations use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Exact per-declaration sets are in the audit and summary. No custom axiom, `sorryAx`, or compiler-trust reduction axiom occurs in those dependencies.
- A source scan found no `sorry`, `admit`, `native_decide`, custom axiom, `run_elab`, or unsafe declaration in the mathematical modules.
- Batch kernel replay successfully checked **633 declarations from all four mathematical modules**, including the external finite proof, with a Mathlib-only initial environment.
- The source, toolchain, build, axiom-audit, and replay commands all exited zero.
- Repository validation, Markdown links, immutable-history checks, deterministic data generation/check, and all **22** unit tests passed.

## Reproduction and evidence

From the package directory:

```sh
python3 fetch_source.py
lake exe cache get
python3 verify.py
```

`verify.py` checks exact source identity, builds, checks the axiom allowlist and expected theorem names, and verifies the complete replay module list and successful counts. It writes actual logs, exits, timings, and source hashes under the ignored `logs/` directory. An earlier successful summary is removed before a new run starts.

Public evidence copies are indexed by artifact ID, SHA-256, and byte count in [artifacts.json](evidence/artifacts.json):

- [Empty-directory source fetch](evidence/fresh-source-fetch.log), [source identity](evidence/sources.log), and [toolchain](evidence/toolchain.log).
- [Finite-core and compactness source build](evidence/initial-build.log), [successful full package build](evidence/general-build-fixed.log), and [final verification build](evidence/build.log).
- [Exported types and transitive axiom audit](evidence/axioms.log), [full kernel replay](evidence/replay.log), [actual commands](evidence/commands.json), and [verification summary with source hashes](evidence/verification-summary.json).
- [22 unit tests](evidence/awards-tests.log), [validation](evidence/awards-validate.log), [data generation](evidence/awards-build.log), [data consistency](evidence/awards-check.log), [history](evidence/awards-history.log), [links](evidence/awards-links.log), and [repository command records](evidence/repository-commands.json).

The public copies replace only the local absolute workspace prefix with `<WORKSPACE>`; original logs remain locally. The external finite source remains at its pinned upstream location, as recorded in [source-manifest.json](source-manifest.json). It is not bundled into the PR.

## Verification scope

The imported Mathlib dependencies use official caches, reused locally from the earlier JSP-000078 verification. None of that earlier submission's custom proof outputs is a dependency of this package. The finite proof and all new mathematical modules were built locally; the final build reuses their unchanged compiled outputs.

[ReplayBatch.lean](ReplayBatch.lean) collects the exported, server, and private declaration data from `ErdosProblems.Erdos922`, `Jsp000766.Compactness`, `Jsp000766.General`, and `Jsp000766`. It calls the unchanged Lean `Environment.replay` API against an environment importing Mathlib only. The checker rejects custom axioms, unsafe/partial declarations, and names overlapping the initial environment or another collected module. None of the four checked modules is accepted as a trusted imported premise.

The replay checks declaration dependencies and regenerated inductive definitions using the **same Lean kernel**. It is not a fresh replay of all Mathlib, an independently implemented kernel, an independent human referee report, or an official prize verification. The checking utility uses Lean's unsafe environment API but is not imported by the mathematical proof.

Lake's cached-build messages containing “Replayed” are distinct from this explicit kernel replay. References and original checker notices are retained in [REFERENCES.md](REFERENCES.md).
