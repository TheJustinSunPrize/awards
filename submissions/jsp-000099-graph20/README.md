# JSP-000099: the 20-vertex witness for the known bound G(6) ≥ 21

This submission provides a GPT-assisted Lean formalization of a known finite result associated with [Erdős #82](https://www.erdosproblems.com/82). It proves that an explicit simple graph on 20 vertices has no regular induced subgraph on six or more vertices. The original mathematics and graph construction are due to Paul W. Dyson and Brendan D. McKay, [Theorem 1.2](https://arxiv.org/html/2604.08215v3). No new mathematical bound, global first-formalization priority, prize eligibility, or award decision is asserted.

The main theorem is `Graph20Proof.exists_graph20` in [Graph20Result.lean](Graph20Result.lean). Its types use Mathlib's `SimpleGraph`, `induce`, and `IsRegularOfDegree`. Every subset of size 6 through 20 and every natural-number degree is quantified, including degree zero and disconnected regular graphs. See [STATEMENT.md](STATEMENT.md) for the exact statement and its relation to the problem.

## What is included

The package contains the explicit graph, twenty generated certificate modules, the final theorem assembly, two finite checking algorithms, certificate generation, negative controls, axiom auditing, reproduction instructions, and verification logs. The twenty certificates contain 10,847 nodes. The original graph6 record and its source are pinned by SHA-256.

The generic certificate checker and four supporting modules come from [PR #190](https://github.com/TheJustinSunPrize/awards/pull/190), commit `4022d2df0f941a12f497d5045b75995e0cf8f883`. Their contribution is essential and is not claimed as an independent invention. The original five files are referenced rather than redistributed while their license scope is clarified in [this inquiry](https://github.com/TheJustinSunPrize/awards/pull/190#issuecomment-5704109522). The retrieval script checks their upstream hashes and produces exactly the five assembled module hashes used in the local verification. The fetched originals, notices, and assembled files are ignored by Git. This is a reproducible package with external source dependencies, not a self-contained source archive. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Reproduction

Use Python 3.11 or later and Lean 4.34.0. Add that toolchain's `bin` directory to `PATH`, including its `leanchecker` and `leantar` executables. From this directory:

```sh
python3 fetch_upstream.py
lake update
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Finite Mathlib.Data.Fintype.Fin Mathlib.Data.Finset.Card
python3 verify_witness.py
python3 verify_formal.py --lean-bin /path/to/lean-4.34.0/bin
```

The first command downloads the pinned external sources and notices. For copies already obtained from that revision, use `python3 fetch_upstream.py --source-dir /path/to/upstream-files` instead. Retrieval grants no additional license to the external sources. The output hashes must match [upstream-sources.json](upstream-sources.json).

Keep [lake-manifest.json](lake-manifest.json) pinned. The verification script refuses dependency revisions that differ from it; Mathlib is fixed to `5ed2965256430c3649e86755f9576b54eca72435`. The script regenerates all certificates byte for byte, compiles, runs negative controls, checks the final theorem axiom closures, and runs `leanchecker --fresh --verbose Graph20Result`. The Lean source and dependency hashes are recorded in [verification/formal-verification.json](verification/formal-verification.json).

## Verification and limits

Local checks passed for all 1,026,876 subsets of order at least six using two algorithms. The Lean modules compiled; the two final theorem axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`. Fresh Lean kernel replay passed. The declarations use kernel-checked certificates rather than trusting the Python search output. Negative controls reject false leaf and checkpoint claims. The exact logs and stage exit codes are included.

`leanchecker` uses the Lean kernel; it is not an independent checker implementation. No Nanoda run, organizer-designated verification, all-dependencies-from-source rebuild, or independent network-isolation audit is claimed. Dependency caches were used. The supporting Python exploration of adding one vertex is outside the formal theorem: it excludes extensions of this one fixed graph only and does not prove G(6) = 21.

## Requested review and attribution

Related discussion: [issue #51](https://github.com/TheJustinSunPrize/awards/issues/51), [the scope inquiry](https://github.com/TheJustinSunPrize/awards/issues/51#issuecomment-5704109103), and [PR #190](https://github.com/TheJustinSunPrize/awards/pull/190). PR #190 concerns the distinct 29-vertex bound G(7) ≥ 30. This contribution addresses G(6) ≥ 21. Neither finite result settles the open asymptotic question.

Please review statement fidelity, the reproducibility evidence, attribution, and whether this additional formalization of a known finite subresult is assessable under JSP-000099. The submitter has an interest in possible recognition for the additional formalization work. Recipient identities, prize allocation, eligibility, and priority remain for the organizers to determine. This directory creates no candidate or award record and changes no published problem or decision status. The generic verifier's credit and the original mathematical authors' credit are preserved.
