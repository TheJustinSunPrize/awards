# JSP-000692 / Erdős 836: both questions

This submission formalizes both finite-hypergraph questions of [JSP-000692](../../problems/catalog-0601-0700.md#JSP-000692) in Lean 4.19.0. It is submitted for proof, statement, contribution, priority and prize-eligibility review. Related tracking issue: [#50](https://github.com/TheJustinSunPrize/awards/issues/50).

## Proved statements

**Question 1: no uniform O(r²) vertex bound.** For every real coefficient C and natural threshold R, the proof constructs an r-uniform intersecting hypergraph of chromatic number exactly 3, with r >= max(2,R), whose active vertex count exceeds C*r². Every ambient vertex occurs in an edge. The construction exists at every r >= 2 and has at least 2^(r-2) active vertices.

**Question 2: a linear intersection bound.** Every eligible finite hypergraph has distinct edges E and F with `r <= 2 * |E ∩ F| + 1`, hence `r/3 <= |E ∩ F|`.

The combined declaration is `JSP692.jsp000692_complete`; `JSP692.jsp000692_complete_explicit` expands both answers and all quantifiers. See [the mathematics](MATHEMATICS.md), [statement correspondence](STATEMENT_REVIEW.md), [modules](JSP692/Complete.lean), and [standalone source](JSP000692.lean).

## Reproduce the verification

Install the toolchain in `lean-toolchain`, then run from this directory:

```sh
python3 scripts/verify.py --prepare
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/finite_checks.py
```

Lean is pinned to 4.19.0. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine dependencies are locked. If an older native cache executable fails to load on macOS, fetch its cache through the Lean interpreter and run without `--prepare`:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
python3 scripts/verify.py
```

The verifier builds all modules, prints and checks all 67 theorem axiom reports, prints the definitions and final theorem types, and independently elaborates the single-file version importing only Mathlib. Modular and standalone declarations intentionally have the same names; do not import both together.

## Actual evidence and limitations

The [machine receipt](verification/status.json) records the successful local run. The [publication review](verification/publication-review.json) binds the evidence to final source hashes. All 67 audited declarations use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Source scans reject proof placeholders, added axioms and native-computation escapes. Compiler warnings concern unused section variables only.

The original both-question candidate needed one type-inference repair: two occurrences of `liftCore s` in `insert_liftCore_card` became `liftCore (Y := Y) s`. The [exact patch](verification/local-fix.patch) changes no mathematical condition or conclusion. The standalone source was regenerated from the modules. Any NOT COMPILED comments in the source describe the original authoring environment; the current dated run supersedes them.

Finite regression checks and 11 verification-utility tests are supplementary. The proof covers finite hypergraphs, not a separately formalized infinite-family compactness extension. The first answer needs only an exponential lower bound; the exact central-binomial vertex formula and sharp asymptotic count are not formalized.

Evidence is submitter-produced with AI assistance. It is not an independent human review, independent second-checker certificate, organizer acceptance or award decision. Repository CI validates repository records and does not execute this Lean proof. False `independent_*` and `award_*` fields in the verifier receipt describe what that script does not establish; submission is evidenced by the public PR.

## Attribution and requested assessment

The submitting account is randyxian08; preparation and review used OpenAI Codex assistance. The proposed formalization recipient placeholder is `RECIPIENT-JSP-000692-A`, pending confirmation. The submitter has an interest in assessment of this formalization contribution.

The first construction is credited to **Noga Alon**, as recorded on the [original problem page](https://www.erdosproblems.com/836). This submission formalizes that existing mathematics.

[Liam Price's 27 April 2026 forum post](https://www.erdosproblems.com/forum/thread/836#post-5941) reports a GPT-5.5 Pro solution of the second question. Its linked manuscript has not been fully compared with this argument. No mathematical discovery or first-formalization priority is claimed. Please consider prior contributions and overlapping formalizations when assessing attribution and eligibility.

Please review both statements, the proof and its reproduction, and the contribution's eligibility under the published rules. The directory is a proposed intake location. Official candidate, recipient, catalog and award records remain for maintainers to determine.
