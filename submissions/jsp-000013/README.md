# JSP-000013: certified Hadamard matrix of order 716

## English

This submission formalizes the existence of a **716 by 716 integer Hadamard matrix**.
The final declaration is `Hadamard716.hadamard_716_exists_standard` in
`src/StandardStatement.lean`, using Mathlib's standard `Matrix.IsHadamard` predicate.
Its entries are signs and both its row and column Gram matrices equal `716 I`.

This is a finite special case of
[JSP-000013](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000013).
The general conjecture is not solved, and the catalog must not be marked Solved or
eligible for a complete-solution award on this evidence. The requested review scope
is the **order-716 formalization as partial progress**, with eligibility and attribution
left to the organizers. No award, priority acceptance, or recipient confirmation is claimed.

## Attribution and distinct contribution

- The matrix was announced in August 2026 by Levent Alpoge, Philippe Voinov and
  Saul Reynolds-Haertle with disclosed Claude assistance. This submission does not
  claim mathematical discovery. The independently reproduced matrix data are pinned
  to [hoa64 commit d825201](https://github.com/bbeartheancient/hoa64/blob/d825201089123126ce792d4921cba4ae1b8977a3/matrices/hadamard_716.csv.gz).
- The proof architecture is adapted under Apache-2.0 from Arthur Freitas Ramos,
  David Barros Hulak and Ruy J. G. B. de Queiroz's
  [order-668 formalization](https://github.com/Arthur742Ramos/hadamard-668-lean/tree/78fbae8d69b6fdb66705b662469692d60e346ef0).
  Their existing order-668 result is prior art, not a result of this submission.
- New work in this package is the different order-716 certificate, reconstruction
  and exact comparison to the matrix data, recomputed correlation tables and their
  Lean checks, adaptation to order 716, and the bridge to Mathlib's standard predicate.
  This is a derivative formalization with explicit prior-work credit, not an independently
  invented proof architecture or a claim of globally established first priority.
- The adapting applicant used OpenAI Codex. For any candidate record, the adapting
  applicant remains `RECIPIENT-JSP-000013-A` pending confirmation. Public source
  authors listed above are attribution references, not confirmed award recipients.
  The applicant has an interest in recognition of this contribution; no reviewer
  independence is asserted.

See `NOTICE` and `LICENSE` for retained attribution and licensing.

## Reproduce

Use the pinned Lean 4.33.0 toolchain and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` from `lakefile.toml`.

```sh
lake update
lake exe cache get
lake build StandardStatement
lake env lean src/StandardStatement.lean
python3 verify_certificate.py
```

The Lean certificate checks use `decide`; the solution contains no `sorry`, custom
axioms, `native_decide`, or `Lean.ofReduceBool`. Final build and axiom-audit evidence
is recorded in `verification.log`. These are local checks, not the organizers'
designated isolated verification or an independently implemented Lean kernel.

The separate Python verifier reconstructs all 512,656 entries from the Lean data,
compares them with the source CSV, checks all 255,970 distinct row pairs exactly,
and performs 8,592 direct integer dot-product checks. It also rejects a single-entry
corruption and accepts whole-row sign reversal. Python output is not trusted by Lean.

## Statement and certificate structure

Four explicit top rows and four families of 178 cyclic rows define the matrix.
The correlation tables contain only natural numbers; every table is proved equal
to its defining finite computation in Lean. The symbolic lemmas reduce arbitrary
row pairs to these checked tables, prove sign entries and row orthogonality, and
then use Mathlib's proved one-sided-to-two-sided Hadamard theorem.

The source CSV SHA-256 is
`52028dbb9a937fdb82b8b09c29a0dcda9502d378550b99649e16185555c0007d`.

## Duplication review and limitations

`dedup-report.json` records the reviewed issue/PR snapshot, changed-file paths and
available patches, and review coverage. Searches included bodies and comments,
not only titles. Initial problem-bank imports and general index maintenance contain
the Hadamard entry; they were distinguished from mathematical submissions.
No dedicated Hadamard submission was found in the reviewed snapshot. Public code
search located the order-668 proof above; searches for a completed order-716 Lean
proof found no relevant result. Search coverage cannot prove universal absence.

The important eligibility uncertainty is whether this particular derivative
formalization of a finite case receives recognition under the organizers' partial
progress and attribution rules. Its connection to an existing JSP entry removes
the need to invent an identifier, but does not resolve that adjudication question.
