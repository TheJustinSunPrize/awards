# Erdős 939 / JSP-000780: Cohn's all-noncube strengthening

This submission formalizes a known result of Cohn (1998). It makes no claim
to new mathematics or an award decision.

`Erdos939.noncube_triples_infinite` proves that infinitely many natural-number
triples `(a,b,c)` satisfy all of the following:

- all three entries are positive and `a+b=c`;
- all three pairs are coprime;
- every prime divisor of each entry has its cube dividing that entry;
- each entry is separately not a perfect cube.

`Audit.lean` expands the powerful and noncube predicates. The final theorem
has no unproved seed, recurrence, growth, or other mathematical hypotheses.
Other higher-power questions within Erdős 939 are outside this package.

## Proof and attribution

The base recurrence is adapted from [inoader's PR #65](https://github.com/TheJustinSunPrize/awards/pull/65),
at commit `b5b70857b2d77d6a060e00956beb8e19918b48f9`, with the Apache-2.0
license and notices preserved. The port to Lean 4.33.1 adds one `norm_num`
step for a numerical side goal in the original seed.

The new module proves that a positive cube factor can be cancelled from
an equation `a*b^3=c^3`. Hence multiplying a noncube by a positive cube
preserves being a noncube. This property is preserved by swapping the
two summands and by the upstream recurrence. The recurrence increases
the third coordinate strictly, contradicting a maximum if the set were finite.

The new seed was checked against page 439 of J. H. E. Cohn,
*A conjecture of Erdős on 3-powerful numbers*, Math. Comp. 67 (1998), 439–440,
[DOI](https://doi.org/10.1090/S0025-5718-98-00881-3),
[Leiden mathematics scan](https://pub.math.leidenuniv.nl/~smitbde/edu/bachsem/3-powerful_abc-triple.pdf).
Lean proves all required seed properties; auxiliary Python computations
are not proof assumptions. See [scope and prior work](SCOPE_AND_PRIOR_ART.md).

## Reproduction

Lean 4.33.1 and all nine dependencies are pinned. Mathlib is fixed at
`0df444a360eaa60ab8c11dca51a86af692955474`. With the specified Lean/Lake
toolchain installed and on PATH, run from this directory:

```text
lake exe cache get
python test_verify.py
python verify.py
```

Alternatively pass `--lean-bin` to `verify.py`, naming the directory containing
`lean`, `lake`, and `leanchecker`. The verifier checks dependency revisions and
clean status, recompiles three project modules with warnings treated as errors,
checks six axiom reports, runs three negative fixtures, and performs
`leanchecker --fresh`. Its results are bound to source/configuration SHA-256
hashes and a unique run identifier. RUNNING is written before tool detection;
completion is published atomically, and older local records are archived.
The six Python regression tests check this record lifecycle, not mathematics.

## Recorded validation

Final run `0dcac7b76bd84c479fe61297eefafbe1` passed with exit code 0.
The allowed axiom set is `propext, Classical.choice, Quot.sound`.
Official dependency caches were used; not all of mathlib was rebuilt.
Fresh replay uses the same Lean kernel, not a second independent implementation.
No second kernel implementation was run.

This English candidate changes only documentation and adds the PR draft and
an export record. Its eight checked source/configuration files are byte-for-byte
identical to the files bound by that verification run. No new Lean compilation
is claimed for this documentation-only export. Logs remain labeled
[redacted copies](REDACTION.md); original failures and verification limits
are preserved. No `.lake`, toolchain binaries, or private raw logs are included.

Permanent archival and organizer review remain pending. Immutable source and release references are recorded in the accompanying pull request when published.
