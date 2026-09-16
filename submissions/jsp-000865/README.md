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

Use Lean 4.33.0 and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. All dependency revisions are pinned in `lake-manifest.json`.

```text
python bootstrap_upstream.py
lake exe cache get
lake build JSP000865.ZeroCapacity
lake env leanchecker --verbose JSP000865.Upstream
lake env leanchecker --verbose JSP000865.ZeroCapacity
```

The bootstrap fetches the unchanged third-party prerequisite from its immutable public URL and checks its SHA-256. It is not silently relicensed or represented as newly authored source. The tested Windows checkout used CRLF while the Git blob uses LF; both hashes and their normalized equivalence are recorded in `upstream-pin.json`.

The build prints the axioms of all submitted targets. See the accompanying evidence files for the actual local results and exact limitations. `leanchecker` replays declarations with the Lean kernel; it is not a second independently implemented proof checker. The semantic review was performed by another AI agent, not by a designated prize curator or a human verifier.

## Attribution and review status

New supplement prepared with Codex assistance on 2026-09-16. Any recipient entry must remain `RECIPIENT-JSP-000865-A`, with confirmation pending, until the operator obtains confirmation. Public source attribution above is provenance, not a nomination made on another person's behalf.

This is a proposed proof-intake path because the repository has not yet documented a dedicated submissions directory. No candidate, award, claim status, curator signature, verifier signature, or recipient confirmation is created by this package. Designated statement review, independent checker requirements, isolated offline review, archival requirements and prize eligibility remain for the operator. The 2026 time boundary and solver/formalizer allocation do not imply payment.

Public code search and the current official PR queue were checked for an existing zero-capacity completion. No matching complete public supplement was identified in those checked sources. This is a bounded search result, not proof that no such work exists anywhere.
