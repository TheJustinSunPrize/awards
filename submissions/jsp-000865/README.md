# JSP-000865: zero-capacity boundary completion

This intake package extends the existing Lean formalization of Erdős Problem 1042 to the omitted zero-transfinite-diameter case. It is an incremental contribution based on existing mathematics and formalization, not a claim of a first formalization, a new solution to the whole problem, or an award entitlement.

## Statement

Let `K` be a closed bounded subset of the complex plane with transfinite diameter `d < 1`. There exist `c > 0` and `N` such that, for every `n >= N` and every list of `n` roots in `K` (with multiplicities), the open unit lemniscate of the associated monic polynomial has at most `(1-c)n` connected components.

The new target `Erdos1042.closed_subunit_transfiniteDiameter_hasUniformComponentGap` states this with the upstream definitions unchanged. `Erdos1042.zero_transfiniteDiameter_hasUniformComponentGap` is its zero-diameter specialization. `Erdos1042.erdos_1042_including_zero` combines the strengthened clause with the two existing resolution clauses.

The assertion concerns all sufficiently large degrees. It does not assert the strict component gap for every positive degree: degree one is an immediate reason that an eventual threshold is needed. Empty sets and repeated roots are included; no distinct-root condition has been added.

## Existing work and exact change

- Original problem: Erdős, Herzog and Piranian, 1958, Problem 6, printed page 139: [original paper](https://users.renyi.hu/~p_erdos/1958-05.pdf). The second question asks about diameter below one, with sufficiently large degree.
- Mathematical foundation: Subhajit Ghosh and Koushik Ramachandran, *Number of components of polynomial lemniscates: a problem of Erdős, Herzog, and Piranian*, [arXiv:2312.13673](https://arxiv.org/abs/2312.13673), later J. Math. Anal. Appl., DOI [10.1016/j.jmaa.2024.128571](https://doi.org/10.1016/j.jmaa.2024.128571). Their stated general gap theorem assumes positive capacity; the zero boundary here is an extension of the argument, not a quotation of their theorem.
- Existing Lean source: [plby/lean-proofs, pinned commit](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1042.lean). Its source credits the mathematical authors above and Codex/GPT-5.6 Sol for the formalization. Its general component-gap clause assumes `0 < d`; its connected-small-capacity clause already includes connected zero-capacity sets.

The supplement replaces the positive comparison level `(d+1)/2` by `(max d 0+1)/2`. This supplies a positive Fekete comparison level below one for every `d < 1`, including `d = 0`. The existing regularization and compactness argument then gives the same uniform component gap. The supplement explicitly attributes the adapted argument to the pinned upstream source.

The applicability of a license to the pinned upstream 1042 file has not been established by this package. Maintainers should confirm it before redistributing or incorporating the adapted proof. No new license over that third-party argument is asserted here.

## Reproduction

The public `reproduce.py` was actually executed on 2026-09-17 (Asia/Shanghai) from a separate package copy with no upstream source or custom compilation outputs. It fetched the immutable raw LF prerequisite (106961 bytes, SHA-256 `bd9cc4a1ffb9f7930e772de7d2917e4b3e3594b83f1495d8ad006805431f74ea`), compiled both modules into fresh outputs, and explicitly replayed both modules. All four process steps passed. The three submitted targets use only `propext`, `Classical.choice` and `Quot.sound`.

Use Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, and an existing compiled Mathlib checkout at `db584cd6d46c92f209a44c0f1c829460d327499d` with its pinned dependency caches:

```text
python reproduce.py --lean-bin /path/to/lean-4.33.0/bin --mathlib-dir /path/to/mathlib
```

Quote paths containing spaces. The helper checks the Lean revision and Mathlib revision/manifest, discards inherited `LEAN_*` and `LAKE_*` variables, fixes the sysroot and thread count, and excludes the package source directory from the module search path. It builds custom modules in a fresh `.reproduction/` directory. It checks source and existing custom-artifact stability at each step and requires each replay log to name exactly the requested module. Coordinate any shared-machine Lean mutex outside the helper.

`bootstrap_upstream.py` checks both the byte count and SHA-256 before use. It refuses an unexpected existing prerequisite instead of overwriting it. Actual negative checks for corrupted existing bytes and a length mismatch are included in the new evidence directory. Downloading the dependency does not establish its license or resolve the uncertainty concerning the adapted proof.

The exact actual run is in [evidence/public-reproduction-2026-09-17/verification.json](evidence/public-reproduction-2026-09-17/verification.json). A post-run contributor check binds source, helper, bootstrap, pin, tool and log identities in [package-integrity.json](evidence/public-reproduction-2026-09-17/package-integrity.json); [source-manifest.json](source-manifest.json) identifies the public package files. The mathematical supplement remains byte-for-byte unchanged from PR28 head `9580441448ff1ba7151d48f2750d029e1ee4b8bc`, SHA-256 `e115cc1e91d3b5093aaade063043c11ac25b32db7af943485559b7edbda36bb5`.

The older `evidence/verification.json` and logs are retained unchanged as historical evidence. Their prerequisite used the Windows CRLF identity `10fb91b2f8e43418adb8bde402e7f1d15d769c5267a72aa813bf42b000e47817`; they are not relabeled as a test of the downloaded LF bytes. Both identities and their normalized equivalence remain in `upstream-pin.json`. The new record above is the fresh end-to-end run of the final public helper. An earlier successful helper trial preceded the environment/search-path tightening; it is not substituted for this final run.

The ordinary Lake route is also configured:

```text
python bootstrap_upstream.py
lake exe cache get
lake build JSP000865.ZeroCapacity
lake env leanchecker --verbose JSP000865.Upstream
lake env leanchecker --verbose JSP000865.ZeroCapacity
```

Existing Mathlib/dependency binaries remain the imported trust boundary. This isolates custom project outputs; it is not a full dependency rebuild or a network-disabled run. `leanchecker` uses the same Lean kernel, not a second independent implementation. Contributor-side checks and separate AI source reviews are not organizer-appointed verification or human referee attestations.

## Attribution and review status

New supplement prepared with Codex assistance on 2026-09-16. Any recipient entry must remain `RECIPIENT-JSP-000865-A`, with confirmation pending, until the operator obtains confirmation. Public source attribution above is provenance, not a nomination made on another person's behalf.

This is a proposed proof-intake path because the repository has not yet documented a dedicated submissions directory. No candidate, award, claim status, curator signature, verifier signature, or recipient confirmation is created by this package. Designated statement review, independent checker requirements, isolated offline review, archival requirements and prize eligibility remain for the operator. The 2026 time boundary and solver/formalizer allocation do not imply payment.

Public code search and the current official PR queue were checked for an existing zero-capacity completion. No matching complete public supplement was identified in those checked sources. This is a bounded search result, not proof that no such work exists anywhere.
