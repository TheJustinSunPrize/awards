# Candidate review: Erdos 96 (JSP-000109)

## English

Draft candidate request. Prize verification, statement review, recipient confirmation and award evaluation are pending. This record does not announce an award or claim accepted entry into evaluation.

### Claim and scope

The submitted result disproves the conjecture that the maximum number of unordered unit-distance pairs among n points in strictly convex position is O(n). The joint construction establishes a lower bound of order n log log n. It does not determine the exact optimal asymptotic growth rate of that maximum. The requested assessment concerns this disproof, with the scope of the broader catalogue question left for the organisers to determine.

Original problem: [Erdos 96](https://www.erdosproblems.com/96). Prize catalogue: [JSP-000109](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000109).

### Pinned proof and supporting evidence

- [Joint proof repository at the submitted commit](https://github.com/Leeham06972452/erdos-96-97/tree/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2)
- [Manuscript PDF](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/96-97.pdf)
- [Manuscript TeX source](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/96-97.tex)
- [Complete Lean proof](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/Erdos9697Complete.lean)
- [Pinned Lean toolchain](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/lean-toolchain), [Lake configuration](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/lakefile.toml), and [dependency manifest](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/lake-manifest.json)
- [Public GitHub Actions build](https://github.com/Leeham06972452/erdos-96-97/actions/runs/34759770555)

The main declarations for this entry are:

- [`Proof.erdos_96_false`](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/Erdos9697Complete.lean#L2416)
- [`Proof.large_convex_counterexample`](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/Erdos9697Complete.lean#L2396)
- [`Proof.convex_unit_distances_omega`](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/Erdos9697Complete.lean#L4606)

The source commit is `0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2`. The proof uses Lean `v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Its only import is `Mathlib`.

To reproduce the source build after installing Lean through elan:

```sh
git clone https://github.com/Leeham06972452/erdos-96-97.git
cd erdos-96-97
git checkout 0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2
lake exe cache get
lake build
lake env lean Erdos9697Complete.lean
```

The proof file includes an axiom audit for 33 declarations and accepts only `propext`, `Classical.choice`, and `Quot.sound`.

### Supplementary local checks

Local automated checks on 2026-09-16 reproduced the source build, audited all 33 declarations, checked the final statements and nonvacuity witnesses, and replayed the module through Lean's `leanchecker`. All completed with exit code zero; the build emitted eight nonfatal linter warnings. No additional axiom or `sorryAx` was reported. The proof source was unchanged.

These are supporting local checks. The dependency build used Mathlib's cache; the run was not the prize's isolated verification. `leanchecker` uses the Lean kernel and is not a distinct independent checker implementation. Broad external peer verification is not claimed.

The local evidence bundle has not yet been deposited in a permanent public archive. An archive identifier and final verifier record must be supplied through the organisers' review process before this draft is treated as completed verification evidence.

### Relationship between the entries and requested review

The same construction supplies the dense convex unit-distance graphs used for the result in JSP-000110. This is a joint proof package, not two independent discoveries.

The submission requests review of both JSP-000109 and JSP-000110 using one pinned manuscript and proof repository. Please confirm whether this shared package is acceptable, whether the records should be handled in one or separate PRs, and how the related results can be evaluated. No entitlement to two awards is asserted.

The formal evidence reference remains null because no official verifier record or curator-signed statement review has been completed. Please assign statement reviewers and verifiers and advise on the required permanent evidence archive. No review signature, independent checker result, or written recipient confirmation has been invented.

### Provenance and attribution

The [source README](https://github.com/Leeham06972452/erdos-96-97/blob/0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2/README.md) and manuscript retain the work's authorship, references and AI disclosure. The manuscript discloses GPT 6 Astra's involvement in the construction, subsequent development and exposition, with responsibility retained by its human authors. Formal Conjectures attribution and its license reference remain in the proof source. This draft links to that source without relicensing or altering it.

Prize-recipient identities remain placeholders. The draft does not assign individual solver/formalizer shares or establish an authorised team representative or payee. The two entries refer to the same proposed submitting team.
