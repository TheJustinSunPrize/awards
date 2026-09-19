# JSP-000690: Lean formalization for intake and eligibility review

This package proves the affirmative **chromatic** interpretation of
[JSP-000690](../../problems/catalog-0601-0700.md#JSP-000690), also recorded as
[Erdos Problem 834](https://www.erdosproblems.com/834).
It independently formalizes the explicit nine-vertex construction in Ruiliang
Li, [arXiv:2512.24850v1](https://arxiv.org/abs/2512.24850v1), Theorem 4.1 and
Appendix A. The mathematical construction is Li's; this submission claims only
the new Lean formalization. OpenAI Codex assisted its preparation.

## Scope and status

- [Main.lean](Main.lean) contains the complete source, including the definitions
  and final existence theorem `JSP690.jsp_000690`.
- The simple three-uniform hypergraph has 9 vertices and 22 edges, chromatic
  number exactly 3, and minimum degree exactly 7. Deleting any edge or vertex
  makes the chromatic number exactly 2.
- Every strict edge subhypergraph is also proved two-colourable. A separate
  theorem restricts vertex-deletion colourings to the actual vertex complement.
- [STATEMENT.md](STATEMENT.md) maps the definitions and theorems to the question.
- This is a self-submission for review, not an official verification attestation,
  candidate nomination, award decision, or authorization to pay.

The paper was submitted on **2025-12-31**. This formalization was prepared on
**2026-09-16**. Section 2.5 of the
[published selection rules](https://www.hejustinsun.com/prize/rules) makes the
eligibility of a new formalization of this older result a question for the
Prize Operator. No eligibility is presumed. Please also confirm whether this
submission directory and a standalone Lean/Std toolchain are acceptable.

## Reproduce

Requires Python 3.10+ and the pinned Lean **4.34.0** release, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. The only Lean import is `Std`,
bundled with Lean; there is no Mathlib dependency and no package download.

With the pinned executables on `PATH`, from this directory:

```sh
python verify.py
```

Alternatively supply `--lean /path/to/lean` and
`--leanchecker /path/to/leanchecker`. The script copies the source to a fresh
temporary directory, checks the version, compiles the module, checks all six
printed axiom reports, and replays `Main` with the bundled `leanchecker`.
Any failure returns a nonzero exit status. The script needs no network access.

The [recorded local run](verification.txt) was produced on 2026-09-16 using
the Windows x86-64 release. Repository validation, local links, generation,
data consistency, and history checks passed; all 22 repository unit tests
passed under Ubuntu/WSL (Python 3.14.4). Repository CI does not run this proof.

The optional [check_finite.py](check_finite.py) independently enumerates the
512 binary colourings and regenerates deletion witnesses. This Python check is
supporting evidence; it is not trusted by or imported into the Lean proof.

The main theorem depends only on `propext` and `Quot.sound`. One auxiliary
equivalence theorem additionally uses `Classical.choice`. There are no
unfinished proof placeholders, custom axioms, native evaluation proof
shortcuts, or unsafe proof declarations in the source.

The bundled checker reuses Lean's kernel. Its replay is **not** an independently
implemented checker or independent human review. Official isolated verification,
statement review, and any additional independent checker remain outstanding.

## Attribution and publication

- Mathematical source: Ruiliang Li, as publicly credited in the linked paper.
- Proposed formalization contributor: `RECIPIENT-jsp-000690-A`, identity
  confirmation pending; no recipient profile or curator signature is asserted.
- No private contact information, identity documents, or payment information
  is part of this package.
- The source and supporting explanations were independently written. Only the
  published mathematical construction is reused, with attribution. The paper's
  prose and verification script are not reproduced.
- Repository [code licensing](../../LICENSE) and
  [content licensing](../../LICENSE-CONTENT) apply to this contribution.

This package does not alter problem-bank eligibility flags, candidate records,
award records, or generated indexes. The proposed `submissions/` location is
an intake proposal and can be relocated by maintainers.
