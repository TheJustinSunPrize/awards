# JSP-000301: additional mathlib implementation for review

## Intake request and earlier work

Please review the attached Lean source as a formalization submission for
**JSP-000301**, and advise whether this additional implementation is eligible
for consideration. The [official website](https://hejustinsun.com/prize/about)
asks for a Lean-containing GitHub pull request. This `submissions/` path is
proposed for intake; it is not an established candidate-record location.
Please redirect the package if a different repository or path is required.

[PR #13](https://github.com/TheJustinSunPrize/awards/pull/13), opened on
2026-09-16 at 08:50:14 UTC, already submits another formalization of this result
and predates publication of this source. This submission is an additional
mathlib-based implementation, not a new mathematical discovery or a claim to
first formalization. Its separate directory does not overwrite that PR's files.
No separate recommendation issue is opened for the same problem.

The counterexample `12167, 12168` and its elementary argument were already
published in the prize catalog. Original-source attribution and scope are
retained in [the problem snapshot](evidence/problem-statement.md).
This contribution is formalization and reproducibility evidence only.

## Exact statement and implementation

The formalization negates the assertion that every pair of consecutive positive
powerful integers contains a perfect square. It uses mathlib's `Nat.Prime` and
`IsSquare`, with unbounded quantifiers over natural prime divisors and square
roots. It proves general lemmas for positive squares, cubes and products of
powerful numbers, and rules out squares between consecutive squares.

- [Pinned definitions and assertion](https://github.com/Redchar1992/jsp-000301-lean/blob/94c99f824c0deb2f0a163ba1b07ad95c7995100d/JSP301/Proof.lean#L19-L25)
- [Pinned counterexample and expanded final theorem](https://github.com/Redchar1992/jsp-000301-lean/blob/94c99f824c0deb2f0a163ba1b07ad95c7995100d/JSP301/Proof.lean#L81-L100)
- Final declarations: `JSP301.jsp_000301` and `JSP301.jsp_000301_expanded`.
- This is not an infinitude or asymptotic counting claim, nor a solution of the
  different question in Erdős problem 365.

## Source and external evidence

| Field | Value |
| --- | --- |
| Source commit | `94c99f824c0deb2f0a163ba1b07ad95c7995100d` |
| [Versioned release](https://github.com/Redchar1992/jsp-000301-lean/releases/tag/v0.1.0) | `Redchar1992/jsp-000301-lean`, tag `v0.1.0`, release ID `389796004` |
| [Source archive](https://github.com/Redchar1992/jsp-000301-lean/releases/download/v0.1.0/jsp-000301-94c99f8.zip) | `jsp-000301-94c99f8.zip`, GitHub asset ID `567652758` |
| Archive SHA-256 | `33b35dc4507b575d7d4f4db36c82b7ef53c8d6ddb612720c2ea68b45486300cf` |
| Archive byte count | `14184` |
| Lean source SHA-256 | `135c5492ebad9f36484cbdebf44210a69559f77e41e067f44a388b60866c1ab2` |
| [Verification log](evidence/verification.txt) SHA-256 | `0fce0c42014d660c15b6b22c37916719cbafbe20372fc4df5fe8d4df29222c0c` |
| Verification log byte count | `3115` |

The archive contains the full tracked source snapshot and the small verification
logs, but no toolchain binaries, dependency caches or Git metadata. The copied
Lean source, manifests, scripts and raw evidence match that snapshot byte for
byte; `README.md`, `VERIFICATION.md` and this new note describe the submission.
The archived README records the pre-submission state and is intentionally not
rewritten. A versioned GitHub release is not a permanent DOI archive and is not
configured as immutable. Independently preserved permanent archival remains
pending if required by the reviewers.

## Reproduction and limitations

Install the pinned Lean release through elan, then run from this directory:

```sh
./scripts/lake.sh exe cache get \
  Mathlib.Data.Nat.Prime.Basic \
  Mathlib.Algebra.Group.Even
./scripts/verify.sh
```

Lean `v4.34.0` and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are pinned. The recorded local build,
bundled `leanchecker` replay and seven-declaration axiom audit passed.
The final theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
There are no custom axioms, proof placeholders or native-evaluation shortcuts
in the local proof. See [VERIFICATION.md](VERIFICATION.md) for the evidence.

`leanchecker` uses the same Lean kernel; it is not an independent checker
implementation. Standard upstream mathlib caches were used. There has been no
clean, network-disabled rebuild of the entire dependency chain or independent
human review of statement equivalence. This package does not assert completion
of the official verification-record requirements. Repository CI checks records,
not this Lean proof, and its built-in Markdown link check does not scan the
proposed `submissions/` directory.

## Attribution, consent and record impact

- Codex AI assisted preparation, checking and submission of this implementation.
  This is a self-submission; the submitter has a direct interest in its review,
  and the local checks are not independent review.
- Use `RECIPIENT-jsp-000301-mathlib-A` as a proposed formalizer placeholder
  until authorized recipient confirmation. Public source-hosting URLs identify
  the evidence location; they are not recipient confirmation or publication
  attestations. No private identity, contact or payment material is included.
- No candidate YAML, recipient profile, award tier, curator signature,
  verification attestation, solver credit, eligibility flag or payment status
  is created or changed by this submission.
- The catalog does not establish the problem's original proposal year. No date
  is invented to satisfy a candidate-record schema.
- Reviewers should determine whether this additional formalization has an
  eligible contribution despite the older mathematical result and earlier PR,
  and arrange any required statement review, independent verification,
  permanent archival and recipient confirmation before a record transition.

Submission, local proof checking, repository CI and merging a PR do not by
themselves announce an award or authorize payment.
