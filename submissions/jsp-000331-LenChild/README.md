# JSP-000331: sufficiently large sets and Graham's gcd bound

This package reproduces an existing formal proof of the sufficiently-large-cardinality
inequality in [JSP-000331](../../problems/catalog-0301-0400.md#JSP-000331).
It adds a small statement bridge, pinned dependencies, source integrity checks,
and a reproducible verification procedure. It does not claim a new mathematical
proof or an original formalization of the upstream argument.

The complete source build, six-declaration axiom audit, and fresh-environment
Lean kernel replay passed on 2026-09-17. See [VERIFICATION.md](VERIFICATION.md)
for the results and archived evidence, and `verification-output/result.json`
for the actual result after each local verification run.

## Statement

There exists a natural number `N` such that every nonempty finite set `A` of
positive natural numbers with `N ≤ A.card` contains `a, b` satisfying
`gcd(a, b) ≤ a / A.card`, with the comparison and division in the rationals.

```lean
∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card → 0 ∉ A → A.Nonempty →
  ∃ a ∈ A, ∃ b ∈ A, (a.gcd b : ℚ) ≤ (a : ℚ) / A.card
```

`JSP331.eventual_graham` applies the pinned `Erdos402.erdos_402`.
`JSP331.sufficiently_large_gcd_bound` exposes the complete statement without
the local proposition abbreviation. `JSP331.sufficiently_large_distinct_gcd_bound`
also supplies distinct witnesses by increasing the threshold to at least two.
See [STATEMENT.md](STATEMENT.md) for the scope and definition review.

## Reproduce

Prerequisites: Git, Python 3.10 or later (standard library only), elan, and
network access to GitHub and the official mathlib artifact cache. Put elan's
`bin` directory on `PATH`. All commands below run in this directory.

```sh
elan toolchain install leanprover/lean4:v4.33.0
python scripts/verify.py --bootstrap --cache
```

On Windows, the existing Conda Python environment may be used; no separate
Python packages are required. The verifier defaults `LEAN_NUM_THREADS` to 4
unless it is already set.

The bootstrap downloads pinned sources and checks their SHA-256 hashes. It
applies the pinned upstream compatibility patches, then checks all 126 source
files in the non-mathlib import closure. Mathlib and its own dependencies are
fixed by `lake-manifest.json`. External source code stays under ignored `.lake/`.

The verifier builds the full imported proof from source, prints and checks
the transitive axioms of the PNT interface, the upstream theorem, and the JSP
declarations (including the distinct-witness bridge), then replays the imported
environment with
`leanchecker --fresh JSP331.Proof`. It accepts only `propext`,
`Classical.choice`, and `Quot.sound` in the audited declarations. Missing
audit output, unexpected axioms, source hash mismatches, and failed commands
all fail the verification run.

Logs, exit codes, durations, and log hashes are saved in ignored
`verification-output/`. Subsequent checks use `python scripts/verify.py`.
While a run is in progress, `python scripts/status.py` shows its phase,
current command, and latest log lines. A running or interrupted record is
not a successful verification result.
For a clean proof rebuild, use a fresh copy of this package without `.lake/`
and repeat the commands. Mathlib artifacts may be downloaded; the 126
external proof source files and the JSP wrapper are built locally.

`leanchecker` uses Lean's own kernel. This is a kernel replay, not an
independent checker or external reviewer certification. Repository record
checks are separate from mathematical verification.

## Attribution and licensing

The main argument and formalization are existing upstream work. Our work is
the catalog statement bridge and the reproduction, integrity, and verification
tooling in this package. See [REFERENCES.md](REFERENCES.md) for precise source
commits, author attribution, and the upstream license limitation.

Only our original wrapper, scripts, and documentation are contributed here.
No upstream proof source or compatibility patch is vendored. Downloading
upstream sources does not establish a blanket reuse license for them. The
root repository licenses govern our new contributions, not third-party work.
