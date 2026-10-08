# JSP-000617: formalization of the upper-density variant

## English

This submission supplies machine-checked formalization evidence for the known
upper-asymptotic-density variant of Erdős #749, corresponding to JSP-000617.
Please review its mathematical scope, attribution, and eligibility under the
prize's rules. It is not a claim to have solved the original lower-density problem.

## Result

For every real epsilon > 0, there exists A ⊆ ℕ such that the upper asymptotic
density of A+A is at least 1−epsilon and there exists a single natural constant C
such that every n has at most C ordered representations n=a+b with a,b∈A.

The theorem is `JSP000617.upper_density_variant`. The proof uses actual subsets
of ℕ, ordinary addition, and the standard limsup of prefix densities. It counts
both orders and diagonal pairs. The bound is uniform in n.

- [Pinned final Lean theorem](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fa8d6aa86daec50064d92872d1b366ff9869b573/projects/jsp-000617/JSP000617Upper.lean)
- [Pinned proof outline](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fa8d6aa86daec50064d92872d1b366ff9869b573/projects/jsp-000617/PROOF.md)
- [Pinned statement comparison and definitions](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fa8d6aa86daec50064d92872d1b366ff9869b573/projects/jsp-000617/STATEMENT_FIDELITY.md)
- [Original problem](https://www.erdosproblems.com/749)
- [Source discussion](https://www.erdosproblems.com/forum/thread/749)
- [Current catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000617)

The catalog records progress on the upper-density variant and does not currently
mark this problem eligible to claim. This submission requests review of the
formalization; it does not change that screening marker or announce an award.

## Formalization contribution and attribution

The contribution submitted for review is the Lean implementation, including
finite-field constructions, their transfer to ordinary natural-number packets,
cross-scale representation bounds, an increasing infinite union, and the final
upper-density theorem.

The mathematical upper-density result is attributed to Aron Bhalla, with disclosed
GPT-5.4 assistance. Terence Tao explained the finite-field/parabola and
separated-scale construction in the public discussion. These mathematical
attributions and Mathlib's authorship are preserved. This formalization was
prepared with OpenAI ChatGPT assistance under the submitting account's direction.
It does not claim a new mathematical discovery or establish first-formalization
priority.

Suggested recipient placeholder: `RECIPIENT-JSP-000617-A`.
Written recipient confirmation is pending. This is self-submitted evidence;
no independent human review or organizer decision is asserted.

## Verification evidence

Proof source commit: `fa8d6aa86daec50064d92872d1b366ff9869b573`.

- Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
- [Successful exact-commit verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176762703).
- Nine proof modules compiled and were checked with Lean's checker.
- All 22 selected theorem-axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The source audit rejects `sorry`, `admit`, `native_decide`, new `axiom`
  declarations, and `unsafe` proof declarations.
- Nanoda independently checked 11,534 declarations with no errors, including
  the exported final theorem and its dependency closure.
- Nanoda commit: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
- Lean exporter commit: `6cea97789dc088ea47fcea15692db85685aedac5`.

The complete public job transcript is retained at external Git archive commit
`9bce96e050e4d0312cbf6462316efbb8de6c934a`:
[transcript](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9bce96e050e4d0312cbf6462316efbb8de6c934a/submission-evidence/jsp-000617/verification-job.log)
and [manifest](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/9bce96e050e4d0312cbf6462316efbb8de6c934a/submission-evidence/jsp-000617/manifest.json).

Transcript SHA-256: `fa807ec109586c290d6e946206ccb2f5dec5aeea5c7e424717f3885ff7dd4de2`; size: 39486 bytes.

The larger Actions evidence ZIP has artifact ID `10479590188`, size 8,141,137
bytes, and GitHub-reported SHA-256
`836d21e957b8a65c341c5b1261192df7ea4bcc90f379d8c4c20de4b96e8bd5b9`.
It expires on 2026-12-16. The complete transcript and proof source are retained in
Git; permanent archiving of that entire ZIP/export bundle is still pending.
No completed organizer verification record or human statement-equivalence
attestation is represented by these software-checking results.

Reproduction commands, run inside `projects/jsp-000617` at the proof commit:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

## Requested review and record impact

Please assess this as formalization evidence for the upper-density variant and
advise whether it qualifies for recognition or a candidate record. Review of the
original lower-density problem must remain separate.

This documentation-only contribution changes no problem status, eligibility flag,
live candidate record, recipient profile, published decision, award, or payment.
