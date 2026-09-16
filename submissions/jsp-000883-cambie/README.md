# Erdős 1063: Cambie's least-common-multiple upper bound

This package formalizes **Stijn Cambie's known mathematical result**. It does not claim a new upper bound or a solution of the full open growth-rate question in Erdős Problem 1063 / JSP-000883.

```lean
theorem Erdos1063.erdos_1063.variants.cambie_upper_bound
    {k : ℕ} (hk : 3 ≤ k) :
    Erdos1063.n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id
```

Here `n k` is the least natural number `n ≥ 2*k` for which **exactly one** of `n, n-1, …, n-k+1` fails to divide `Nat.choose n k`. The least common multiple, binomial coefficient, and divisibility are over natural numbers. `cambie_witness` explicitly supplies a member of the defining set, with exceptional offset `0`.

## Reproduce the verification

Run from this directory with Python 3.10 or later (no additional Python packages):

```text
python -X utf8 verify.py
```

The verifier recompiles all three project Lean files and exits unsuccessfully if a required step fails. Put the pinned toolchain's `lake` on PATH, or supply `--lean-bin /path/to/lean/bin`.

The fixed environment is:

- Lean: `leanprover/lean4:v4.33.1`; compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- `lake-manifest.json` pins Mathlib and all eight transitive dependencies. Verification checks their actual Git HEADs and rejects dirty dependency worktrees.
- The original Windows toolchain archive had SHA-256 `f63029c0e1e6daed0f4807481b6fcd8f8b77fbce6d63f205c7f9191072387a7a`.

On a fresh machine with elan configured, `lean-toolchain` selects the required Lean release. First obtain the pinned dependencies and their official compiled cache:

```text
lake exe cache get Mathlib.Algebra.BigOperators.Intervals Mathlib.Algebra.BigOperators.Group.Finset.Piecewise Mathlib.Algebra.GCDMonoid.Finset Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.GCD.Basic Mathlib.Data.Nat.GCD.BigOperators Mathlib.Order.Lattice.Nat
```

Then run the verification command above. The original cache download covered 877 dependency files; one TLS failure was followed by a successful retry. The evidence retains both attempts. Project files were recompiled; **all of Mathlib was not rebuilt from source**. The distributable excludes Lean binaries, `.lake`, and `.git`.

## Verification record and its limits

Final release verification run: **e38f0a6fd3e344dfa4cc67d05e224346**. Final release result: **PASS**.

[logs/results.json](logs/results.json) records the run status, commands, exit codes, versions, dependency commits, and source hashes. [logs/verification.log](logs/verification.log) contains the command transcript. The required checks are:

| Check | Acceptance condition |
| --- | --- |
| `lake build`, then forced compilation of Statement, Cambie, and Audit | Every command succeeds |
| Full target printing, definition alignment by `rfl`, and a separately written explicit target type | All typecheck |
| `#print axioms` for the final theorem, witness, product lemma, and alignment declarations | Each uses exactly `propext`, `Classical.choice`, `Quot.sound` |
| Source scan for prohibited proof constructs | Passes separately from axiom inspection |
| False arithmetic fixture `2+2=5` | Lean rejects it |
| Isolated sorry/custom-axiom fixtures | The axiom acceptance gate rejects both |
| `lake env leanchecker --fresh -v Cambie` | Succeeds |

The axiom policy is an internal acceptance criterion, not an organizer-approved whitelist. Negative fixtures are generated in the Git-ignored `verification-tmp/` directory and are not imported by the proof.

The `leanchecker` options were checked against the installed version's `src/lean/LeanChecker.lean` and `Lean/Replay.lean`. `--fresh` replays checkable declarations in Cambie and its imported environment from an empty environment. The official tool skips unsafe/partial declarations; this package's mathematical proofs contain neither. Replay uses the same Lean kernel: **no checker with a separate kernel implementation was run**. Local verification does not constitute designated organizer verification.

The public distribution contains **redacted copies** of environment-bearing logs and evidence. Original outputs are retained locally and are not published. The export replaces local path prefixes using `<PROJECT>`, `<WORKSPACE>`, `<LEAN_BIN>`, `<PYTHON>`, and `<USER_HOME>` placeholders, matching longer paths first and accounting for Windows path separators and case. See `logs/REDACTION.md` and `logs/redaction-manifest.json` in the public distribution for the implemented rules and affected files. Redaction must preserve failures, exit codes, and verification limitations. Public-copy hashes identify the published bytes; they do not independently authenticate the original run.

## Verifier lifecycle regression checks

Run `python -m unittest -v test_verify.py` to check the verification record lifecycle.
Six regression tests passed, including a missing-Lake attempt seeded with an old PASS,
visible RUNNING state, timeout, log initialization failure, command launch failure,
and atomic-write failure. A new run has a unique ID before tool discovery, archives
previous logs locally, and atomically records its current state. See
[logs/verifier-tests.log](logs/verifier-tests.log).

## Files and contribution scope

- `Statement.lean`: definitions reproduced from the pinned Formal Conjectures source, with Apache-2.0 attribution retained.
- `Cambie.lean`: the product lemma, explicit witness, and formal proof of Cambie's upper bound.
- `Audit.lean` / `verify.py`: statement alignment, axiom inspection, builds, negative tests, and replay checks.
- [PROOF.md](PROOF.md): the mathematical argument corresponding to the implementation.
- [SCOPE_AND_PRIOR_ART.md](SCOPE_AND_PRIOR_ART.md): fixed sources, bounded prior-work screening, reuse, and unresolved eligibility questions.
- `evidence/`: source snapshots or search metadata, outside the Lean import chain.

The addition relative to [PR #56](https://github.com/TheJustinSunPrize/awards/pull/56) is Cambie's least-common-multiple bound; that PR, at the inspected revision, covers Monier's factorial bound. Mathematical credit remains with Cambie. The organizers determine intake, eligibility, priority, and any award allocation.
