# JSP-000621 / Erdős 757

Lean 4.34.0 formalization of the known upper bound `c ≤ 4/7` for the
universal Sidon-subset guarantee in finite `(4,5)`-sets. Local compilation,
axiom audit and fresh-kernel replay have passed. Organizer verification,
priority determination, eligibility and any award remain pending.

The mathematical construction is due to **Jie Ma and Quanyu Tang**,
[Largest Sidon subsets in weak Sidon sets](https://arxiv.org/abs/2602.23282),
Lemma 5.1 and Section 5.1 in version 1. The original optimal-constant problem
remains open. This project does not claim mathematical discovery, a proof of
the lower bound, or a completed award review.

The formal statement concerns all finite sets of real numbers.
Sidon sums include repeated summands `x + x`. The integer certificate must
is connected by proved cast, cardinality and difference-set lemmas to that
real-number statement. The exact scope is recorded in [STATEMENT.md](STATEMENT.md).

Existing public proposal: [TheJustinSunPrize/awards#49](https://github.com/TheJustinSunPrize/awards/issues/49).
No first-formalization or award-priority claim has been established.

## Main result

`SunPrize621.admissible_le_four_sevenths` proves that every real constant
satisfying `SunPrize621.Admissible` is at most `4/7`.
`Admissible c` says that every finite real `(4,5)`-set `A` has a Sidon
subset `S` with `c * |A| ≤ |S|`.

The certificate proves the local difference condition for the authors'
fourteen-point set, proves the absence of a nine-point Sidon subset, and
exhibits an eight-point Sidon subset. Every nine-point subset contains one
of twelve explicitly verified three-term arithmetic progressions. Such a
progression has the forbidden collision `a + c = b + b`.

All finite certificate propositions are discharged using `decide +kernel`.
The proof uses no placeholders, custom axioms, native-evaluation shortcut,
external solver assumption or environment-modification command.

## Reproduce

Requirements: Python 3.10+, Git, and the official Lean 4.34.0 toolchain with
`lean` and `lake` on PATH. `lean-toolchain` and `lake-manifest.json` pin Lean,
Mathlib and every transitive package revision.

Fetch dependencies and the official release cache before the offline checks:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get --cache-from=master Mathlib.Basic.Real.Basic Mathlib.Data.Finset.Powerset Mathlib.Data.Finset.Prod Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith
python3 verify.py
```

The verification script builds the proof, compiles [Audit.lean](Audit.lean)
with warnings treated as errors, checks an axiom allowlist, runs three
negative controls and replays the full imported environment into a fresh
Lean kernel. It writes [evidence/verification.json](evidence/verification.json)
and [evidence/axioms.txt](evidence/axioms.txt).

The audited final theorem depends only on `propext`, `Classical.choice`
and `Quot.sound`. The negative controls ensure that a false arithmetic
claim and a placeholder fail, and that the audit rejects a theorem
depending on a custom axiom even though Lean permits declared axioms.

For a quick rerun, `python3 verify.py --skip-replay` explicitly records
that the fresh replay was omitted from that invocation.

## Verification limits

`leanchecker --fresh` uses the bundled Lean kernel; it is not a separately
implemented proof checker or independent human review. The local checks
used upstream release-cache artifacts, not a complete source rebuild of
all imported libraries. Official designated verification and any required
independent archival remain pending. Repository CI by itself does not
execute or certify this proof.

Code in this package is MIT licensed; imported dependencies retain their
own licenses. When included in the prize repository, documentation and
record data follow that repository's `LICENSE-CONTENT`.
