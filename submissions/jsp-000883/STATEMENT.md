# Statement correspondence

## Original problem and scope

- [Official JSP-000883 record](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000883).
- [Erdős Problem 1063 and source discussion](https://www.erdosproblems.com/forum/thread/1063).
- Monier, Jean-Marie, “Problems and Solutions: Solutions of Advanced Problems: 6447”,
  American Mathematical Monthly 92 (1985), 435–436.
- [Pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean).

The original problem asks for the growth of `n_k`. It remains open. This
submission addresses only Monier's known upper bound, explicitly listed as a
solved variant in Formal Conjectures. It does not prove Cambie's stronger
bound or a new asymptotic estimate.

## Definition fidelity

`Erdos1063.n` is the exact textual definition from the pinned source. It takes
the infimum in the natural numbers over `m ≥ 2k` such that **exactly one** index
`i0 < k` gives nondivisibility and every other index gives divisibility.
It is not weakened to “at most one”. The original source's unproved assertions
are not loaded as dependencies.

The submitted `threshold_spec` establishes that this set is nonempty for all
`k ≥ 2`, and that its infimum satisfies the property. Thus the upper bound does
not arise from the empty-set default value of a natural-number infimum.

## Checked declarations

| Declaration | Scope |
| --- | --- |
| `Erdos1063.monier_upper_bound` | For every natural `k ≥ 3`, `n k ≤ k!`. |
| `Erdos1063.factorial_witness` | `2k ≤ k!`, `k!` does not divide `choose(k!,k)`, and each `k!-i` does for `1 ≤ i < k`. |
| `Erdos1063.threshold_spec` | The least threshold satisfies exactly-one-exception divisibility for every `k ≥ 2`. |

The main theorem has the same type as the pinned
`erdos_1063.variants.monier_upper_bound`, apart from its name and explicit
rather than implicit parameter binder.

## Proof outline

The factorial identity gives
`choose(k!,k) = (k!-1)(k!-2)...(k!-k+1)`.
This proves divisibility by every positive-offset factor. Modulo `k!`, that
product is congruent to `(-1)^(k-1) * (k-1)!`. Its residue cannot be zero because
`0 < (k-1)! < k!`. Hence the zero-offset factor is the unique exception.
For `k ≥ 3`, the witness also satisfies `k! ≥ 2k`.
The threshold bound follows from membership of this witness in the defining
set. The existence statement includes `k=2` using the explicit witness `m=4`.

All quantified parameters are unbounded natural numbers; no finite cutoff,
extra primality assumption, unproved nondivisibility principle, or oracle is used.
