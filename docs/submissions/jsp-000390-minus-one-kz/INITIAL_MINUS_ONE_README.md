# JSP-000390: formalization of the known k = -1 case

## Requested review and scope

Please assess this new Lean formalization of the **already-known special case k=-1**
for formalization-contribution consideration under the published selection rules.
It is not a solution of the full Erdős 479 / JSP-000390 question for all integers
k different from 1, and it is not new mathematical progress on the other residues.
No first-formalization priority, award tier, amount, recipient confirmation, or
entitlement to payment is asserted.

Proposed recipient placeholder: `RECIPIENT-JSP-000390-KZ-A`, confirmation pending.
This is a self-submission prepared with OpenAI ChatGPT assistance under the submitting
account's direction, not an independent referee attestation. Any further professional
conflict disclosures or identity confirmation must be handled through the appropriate
review process; no private identity or payment information is included here.

This directory is a proposed evidence-intake location. No catalog flags, candidate or
award records, recipient profiles, schema, validator, or existing source file is changed.
Please advise on the correct intake location and whether this small known special
case is within the prize's eligible formalization-contribution scope.

## Exact statement

`JSP000390.minus_one_infinite` proves that infinitely many **positive** natural
numbers n satisfy `(2 : Int)^n = -1 (mod n)` using Mathlib's standard `Int.ModEq`
and `Set.Infinite`. The construction is `n=3^r`. Its induction proves the stronger
integer divisibility `3^(r+1) | 2^(3^r)+1`; the proof also supplies a solution above
every natural bound. This is not a finite numerical example or a classification.

See [statement correspondence](STATEMENT.md) and [the source](JSP000390.lean).

## Pinned source and reproducibility evidence

Proof repository: [source project at the exact commit](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/22e9b888c2378df7c2039ceceddccbfc5b883387/projects/jsp-000390-minus-one).

Source commit: `22e9b888c2378df7c2039ceceddccbfc5b883387`.
Proof SHA-256: `4b29e531fbf52e7ac130c16a0d9b03d16057448be5dd113bc06ebc125a4ccec3`.

[Public verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35140570379)
executes the warnings-as-errors build, bundled Lean checker, actual axiom reports
for five targets, a false-arithmetic negative control, and an independently
implemented NaNoda check of the targets and their complete dependency closures.
Consult the actual run and its artifact for the results, not this description alone.

NaNoda's strict allowlist contains only `propext`, `Classical.choice`, and `Quot.sound`;
compiler-trust and native-evaluation axioms are not permitted. Pinned checker source
revisions, export commands, configuration, logs and source hashes are provided by
[the reproducibility scripts](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/22e9b888c2378df7c2039ceceddccbfc5b883387/projects/jsp-000390-minus-one/scripts).

Lean `4.34.0` and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` are pinned;
all transitive dependency revisions are in [lake-manifest.json](lake-manifest.json).
This submitted Lean source and the five project configuration/audit/license files
are copied without changes from the pinned proof project.

Basic reproduction in this directory, with elan installed:

```sh
sha256sum -c SHA256SUMS
lake exe cache get
lake build --wfail
lake env leanchecker JSP000390
lake env lean Audit.lean
```

The same contributor runs both checker implementations. Cached official Mathlib
artifacts and network access are used. A clean network-disabled rebuild of all
Mathlib, independent human statement review, approved minimum safe versions, and
organizer verification are not claimed. GitHub artifact retention is finite;
commit pinning and hashes are not asserted to be independent permanent archival.

## Mathematical attribution and prior-art screening

The [catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000390)
credits reported special cases to Ronald Graham, Derrick Lehmer and Emma Lehmer,
and a public explanatory note to Quanyu Tang. Mathematical credit remains with
the prior literature. Original full question: [Erdős 479](https://www.erdosproblems.com/479).
Related literature: A. Kalmynin, [On Novák numbers](https://arxiv.org/abs/1611.00417).

The existing [rjwalters/lean-genius file](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos479Problem.lean)
proves the k=2 case and explicitly notes its k=-1 case is not formalized. The existing
[Formal Conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/479.lean)
contains the full-question statement, not its proof. Neither source's axioms or
unfinished theorem are imported into this package, and their contributions are
not claimed by this submission.

Official issue and PR searches for `JSP-000390` and `479` on 2026-09-16 returned no
matching entries before this package was prepared. This bounded screening does
not establish absence of all public or unpublished prior work.
