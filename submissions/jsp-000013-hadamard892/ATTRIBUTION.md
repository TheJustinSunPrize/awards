# Attribution and scope

## English

This submission is prepared by [@jinkaizhang236-sketch](https://github.com/jinkaizhang236-sketch) with OpenAI Codex assistance. This identifies the submitting account and disclosed assistance; it does not identify a confirmed prize recipient or announce an award.

The contribution is a new Lean implementation of the classical Goethals–Seidel construction, a concrete certificate from four length-223 sign sequences, and a connection to Mathlib's standard integer `Matrix.IsHadamard` predicate at order 892. The intended final claim is the unconditional statement `∃ H : Matrix (Fin 892) (Fin 892) ℤ, Matrix.IsHadamard H`. Completion and verification claims are governed by the actual verification receipts accompanying the frozen source.

The generic construction is classical mathematics. Discovery of the matrix data is not claimed. The six proof modules were newly written for this contribution; no program source from the order-668 or order-716 formalizations, or from the hoa64 mirror, was copied into these modules. The existing [order-668 Lean formalization](https://github.com/Arthur742Ramos/hadamard-668-lean/tree/78fbae8d69b6fdb66705b662469692d60e346ef0) by Arthur Freitas Ramos, David Barros Hulak and Ruy J. G. B. de Queiroz and the [order-716 submission](https://github.com/TheJustinSunPrize/awards/pull/122) are acknowledged as related earlier work. This acknowledgment does not imply their endorsement or a claim of worldwide first priority.

## Mathematical data

The input is the publicly recorded [order-892 matrix in the hoa64 mirror](https://github.com/bbeartheancient/hoa64/blob/d825201089123126ce792d4921cba4ae1b8977a3/matrices/hadamard_892.csv.gz), pinned to commit `d825201089123126ce792d4921cba4ae1b8977a3`. That commit is dated 16 August 2026. Its [README](https://github.com/bbeartheancient/hoa64/blob/d825201089123126ce792d4921cba4ae1b8977a3/README.md) describes twelve formerly open “Alpoge” orders ingested on 12 August 2026. The dates describe the mirror's recorded history and statement, not an independently established allocation of discovery credit.

The decompressed source CSV has **1,988,714 bytes**, SHA-256 `fa2b9b4bc0d2ab10f6c6422d427e24aefdc5be2c294e95b6476e332af4614ac5`. The four sequences were recovered from the recorded matrix, independently encoded as four integers, and compared entry by entry. In the Lean encoding, bit index zero is sequence index zero, a set bit means `+1`, and an unset bit means `−1`. The reconstructed canonical Goethals–Seidel matrix need not be entrywise identical to the original CSV; the theorem concerns existence at the same order.

We retain the **reported mathematical attribution to Levent Alpöge, Philippe Voinov and Saul Reynolds-Haertle, with Claude assistance**. The complete team credit is publicly recorded in the related [order-716 submission](https://github.com/TheJustinSunPrize/awards/pull/122). The [original Alpöge announcement](https://x.com/__alpoge__/status/2087504785952182273) was not retrievable during this review. The mirror README alone does not list all three names. These are source-attributed credits, not independently confirmed recipient identities, an organizer endorsement, or a claim about the contributors' internal allocation.

## Dependencies and rights

Lean, Mathlib and the verification tools retain their upstream licenses and attribution, as detailed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The new contribution is offered under the receiving repository's terms applicable to submitted material; this statement does not relicense any third-party material. Upstream software licenses are not inferred from the public availability of mathematical data, and no software license is asserted for the hoa64 mirror.

## Prize scope

Order 892 is one finite case of JSP-000013. This work does not settle the Hadamard conjecture for all positive multiples of four. The submission requests review of a scoped formalization contribution. It does not assert organizer-appointed verification, established priority, award eligibility, a prize tier, a confirmed recipient allocation, or a payment entitlement.
