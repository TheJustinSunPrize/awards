# Final source and scope review

## English

An additional Codex agent performed a read-only review of the six production
modules, the pinned Mathlib definitions, the sign encoding and the final
verification outputs. This is an internal review, not an independent human
review or an organizer-appointed verification signature.

The unconditional conclusion has exactly the type
`∃ H : Matrix (Fin 892) (Fin 892) ℤ, Matrix.IsHadamard H`.
Mathlib's predicate requires unitary integer entries and both row and column
Gram equations. Over the integers, unitary entries are precisely the two signs.
No assumption supplies the concrete matrix, its correlations or its
orthogonality. The final reindexing preserves all 892 rows and columns.

The classical block construction is proved generically. Reflection symmetry,
its square, circulant commutation and commutation with transposes are proved in
the bridge. The concrete instantiation discharges all sign and correlation
hypotheses. The 223 separately checked shifts cover every element of `Fin 223`.
The convention is `C(a)[r,c] = a(r-c)` and
`corr(a,t) = sum_x a(x)*a(x+t)`, consistently throughout the production modules.

The four bit-encoded sequences match all 892 sign entries of the recorded seed
data. The readable lists are not an additional unverified assumption: the
theorem computes directly from the bit data. Source attribution is supported by
the separate data audit; the canonical matrix is not claimed to be bytewise
identical to the mirrored CSV.

All six final source hashes match the completed fresh-build receipt. The export
hash and 41,120,305-byte size were recomputed during the final review. All six
compiles, fresh Lean replay, export and Nanoda returned zero. Nanoda reported
9,340 declarations checked without errors and printed only `propext`,
`Classical.choice` and `Quot.sound` as axioms. The three advertised theorem roots
appear explicitly in its output. The separate negative control also compiled
successfully and is outside this three-root export.

No mathematical or scope blocker was found in this review. This does not
establish global priority, original mathematical discovery, official verifier
appointment, nomination, prize eligibility or payment entitlement. Permanent
external archival of the large proof export remains pending.

The bounded public duplicate search through 03:22:15 UTC on 17 September 2026
covered 428 issue/PR records, highest number 429. Its only matching earlier
Hadamard submission was the related order-716 PR 122. No dedicated order-892
submission was found in that search. This is a dated search result, not a
worldwide first-formalization claim.
