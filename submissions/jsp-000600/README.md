# JSP-000600 / Erdős 732: arbitrary truncation profiles

**Partial Progress.** This contribution extends an existing Lean formalization of Alon's construction to every permitted truncation profile over any finite field. It proves an explicit completion formula and an exact count for the resulting family. It does not characterize all block-compatible sequences or claim a new mathematical discovery.

## Exact result

Let `K` be a finite field, `q = Fintype.card K`, and `N = q² + q + 1`. For every `n ≥ N` and multiset `m` of exactly `N` integers in `[3, q+1]`, the theorem `Contribution732.completeProfile_compatible` proves compatibility of

```text
completeProfile n m = m + replicate (choose(n,2) − Σ[a∈m] choose(a,2)) 2.
```

Compatibility is the unchanged `Erdos732.BlockCompatible`: a design on `Fin n`, with all blocks of size at least two and every pair of distinct points in exactly one block. The constructed design's pair-count identity justifies the natural subtraction; nonnegativity of the deficit is not an extra assumption. Each primary block is a subset of a different projective line. Completion adds exactly the uncovered pairs.

`Contribution732.complete_profile_family` constructs a `Finset` of exactly `choose(N+q−2, q−2)` distinct compatible size multisets. This is the size of a constructed family, not the total number of compatible multisets. Filtering entries of size at least three recovers the original profile, establishing injectivity. Stars and bars counts all profiles, including repeated entries without a frequency restriction.

`Contribution732.complete_prime_power_profile_family` specializes to `q = p^k`, for prime `p` and `k > 0`, using Mathlib's actual `GaloisField p k`. It does not assume the existence of an abstract projective plane. Two explicit corollaries are:

| Field order | Ground-set condition | Distinct compatible multisets in the constructed family |
| --- | --- | ---: |
| `q = 4 = 2²` | `n ≥ 21` | 253 |
| `q = 5` | `n ≥ 31` | 5,984 |

## Contribution and prior work

The mathematics is Noga Alon's finite construction in [Theorem 2.3, page 3](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf). At `n=N`, the linewise deficit in the paper equals the displayed formula because `N * choose(q+1,2) = choose(N,2)`. This formalization also permits larger ground sets by completing the remaining pairs. No asymptotic leading-constant result is claimed.

The [pinned upstream implementation](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos732.lean) uses prime `q ≥ 5` and a bounded-frequency code yielding `q^(q−2)` profiles. The new modules remove both restrictions. At `q=5`, the old code yields 125 members; the full profile family has 5,984, and allows all 31 primary entries to equal six.

The complete, untruncated tree of that fixed repository revision was checked for all `Erdos732` paths, including possible submodules. There is no additional solution submodule: the other Lean file is a comparator challenge containing the problem definitions and an unproved target, and is not imported here.

[PR78](https://github.com/TheJustinSunPrize/awards/pull/78) addresses the same catalog entry's upper bound. Its `Design`, `LargeBlocks`, `Encoding` and `Main` modules were inspected at commit `bb4c53e847da438895921ee2290ca19437e08996`; they contain no finite-field profile realization or exact lower-family count. A current two-page search of all 160 public PRs found only that same-entry submission. This bounded comparison does not establish universal priority. No upper-bound work from PR78 is imported or claimed here.

The four new modules are [FinitePlane](Contribution732/FinitePlane.lean), [Profiles](Contribution732/Profiles.lean), [Counting](Contribution732/Counting.lean), and [PrimePowers](Contribution732/PrimePowers.lean). The original upstream file remains an external hash-pinned dependency. [ATTRIBUTION.md](ATTRIBUTION.md) identifies reused arguments, authorship and licensing; the contribution Lean modules use [Apache 2.0](LICENSE-APACHE).

## Validation

The actual fresh Windows run on 17 September 2026 passed all eight verification stages and the serial wrapper with exit code zero. All five custom modules were freshly compiled. The audit produced all 14 requested axiom reports, containing only `propext`, `Classical.choice` and `Quot.sound`, and all six requested definition headers. Two checkers selected exactly four new modules and the one upstream module. The verification stages took 149.341 seconds; no private compiled objects were reused.

[verification.json](verification.json) records the real event times, commands, source and object hashes, actual axiom reports and checker selections. Its eight logs retain their original bytes. Absolute local paths in command metadata use neutral placeholders; the original result digest remains distinct from the public record's digest. The private original result SHA-256 is `fcb20d8aa348bd81a27bfa3ca79054964330f68d048d9bba31e7f513cc443ee3`.

The unchanged executed helper also passed [56 lightweight checks](recipe-checks.json) of metadata, output isolation, HTTP rejection, subprocess planning, audit parsing and failure-stop behavior. These use mocks and are separate from the actual Lean run. Its axiom and definition parser was additionally checked against retained real Lean output, including the `@[reducible]` header used for abbreviations.

## Reproduction

Requires Python 3.10+, Git, Lean 4.33.0 with its matching `leanchecker`, and an already populated Mathlib checkout at `db584cd6d46c92f209a44c0f1c829460d327499d`. The supplied Mathlib and dependency caches are read-only inputs. The helper does not run Lake, install tools or download Mathlib.

```sh
python verify.py
python verify.py --plan --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/new-run
python verify.py --execute --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/new-run
```

Quote Windows paths containing spaces. Default mode checks local metadata, included source hashes and published evidence when present, without network or subprocesses. `--plan` prints commands. `--execute` requires an unused output directory outside the package, Mathlib and runtime, and writes only isolated `src`, `build`, `logs` and `result.json` output.

Execution downloads the single upstream source at its immutable URL, rejects redirects and checks HTTP status, exact URL, byte count, SHA-256 and Git blob ID. It compiles the upstream source and four new modules, compiles [the audit](Audit732Contribution.lean), and runs two checkers. The audit requires 14 named axiom reports and six definition headers. The checker selections must be exactly the four `Contribution732` modules and the one `ErdosProblems.Erdos732` module. [recipe.json](recipe.json) records the complete source and environment contract.

All children receive `LEAN_NUM_THREADS=1`; compilers and the audit receive `-j1 -M8192`. The first failure stops execution and retains its logs. A successful result additionally requires unchanged source, recipe, log and runtime executable hashes. Shared caches remain trusted inputs; they are not freshly rebuilt or fully replayed.

The checker uses Lean's own kernel. No independent kernel implementation, Linux E2E run, human referee attestation, official acceptance, recipient determination or award decision is claimed. This submission was prepared with Codex assistance.
