# Unsigned proposed formal statement

## English

This is a **submitter-supplied, unsigned proposal for review**, not an issued `statement.yaml`. It records no public curator signatures or completed definition reviews. The declarations below are extracted from the source bundled with this generator; an independent reviewer must compare them to [the supplied immutable proof commit](https://github.com/cronrpc/erdos1027-lean/tree/0f0f63749b77195cbd6c1b7f7ef2b11c777663c6) and to [the original question](https://www.erdosproblems.com/1027). The generator validates URL syntax, not remote availability or agreement between its local tree and the supplied commit.

### Scope and quantifier order

For every real c > 0, there exist a real delta > 0 and a natural number N, depending only on c. For **every** finite vertex type V with decidable equality, every natural n >= N, and every finite family F of finite subsets of V, if all members of F have cardinality n and |F| <= c * 2^n, then the number of subsets B of V splitting every A in F is at least delta * 2^|V|. The order is: for every c, there exist delta and N, then for every V, n, and F. There is no regularity, degree, distinct-intersection, nonempty-family, or fixed-vertex-count hypothesis.

The family is a `Finset (Finset V)`, so duplicate edges are not counted multiple times. `Fintype V` supplies finite enumeration; `DecidableEq V` is the equality interface used by finite sets. `Nat.card` is the cardinality of the displayed subtype. Inequalities, delta, c, and the counting bound are in the reals, with the indicated natural-cardinality casts. Choosing V to be the finite union of the edges gives the original ground-set formulation; the theorem allows an arbitrary finite ambient V, including unused vertices.

### Custom definitions to be reviewed

These are exact local source transcriptions, with fully qualified names stated below. They are **not** marked as independently reviewed definitions.

`Erdos1027.Proper`, from [Erdos1027Completion.lean](https://github.com/cronrpc/erdos1027-lean/blob/0f0f63749b77195cbd6c1b7f7ef2b11c777663c6/Erdos1027Completion.lean), means that every edge contains each of the two Boolean colors:

```lean
def Proper {V : Type*} (F : Finset (Finset V)) (u : V → Bool) : Prop :=
  ∀ A ∈ F, ∀ b : Bool, ∃ v ∈ A, u v = b
```

`Erdos1027Subsets.Splits`, from [Erdos1027Subsets.lean](https://github.com/cronrpc/erdos1027-lean/blob/0f0f63749b77195cbd6c1b7f7ef2b11c777663c6/Erdos1027Subsets.lean), means that each edge meets both the selected set and its complement within the edge. In its source namespace the parameters have `{V : Type*} [Fintype V] [DecidableEq V]`:

```lean
def Splits (F : Finset (Finset V)) (B : Finset V) : Prop :=
  ∀ A ∈ F, (A ∩ B).Nonempty ∧ (A \ B).Nonempty
```

The same source proves an equivalence of proper colorings and splitting subsets, with matching cardinalities. Independent statement comparison must review this correspondence as well as the top-level premises.

### Complete Boolean-coloring declaration

Fully qualified theorem: `Erdos1027Main.erdos_1027` in [Erdos1027Main.lean](https://github.com/cronrpc/erdos1027-lean/blob/0f0f63749b77195cbd6c1b7f7ef2b11c777663c6/Erdos1027Main.lean).

```lean
theorem erdos_1027 (c : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (n : ℕ), N ≤ n → ∀ (F : Finset (Finset V)),
          (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
            δ * (2 : ℝ) ^ Fintype.card V ≤
              (Nat.card {g : V → Bool // Erdos1027.Proper F g} : ℝ)
```

### Complete splitting-subset declaration

Fully qualified theorem: `Erdos1027Main.erdos_1027_subsets` in [Erdos1027Main.lean](https://github.com/cronrpc/erdos1027-lean/blob/0f0f63749b77195cbd6c1b7f7ef2b11c777663c6/Erdos1027Main.lean).

```lean
theorem erdos_1027_subsets (c : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (n : ℕ), N ≤ n → ∀ (F : Finset (Finset V)),
          (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
            δ * (2 : ℝ) ^ Fintype.card V ≤
              (Nat.card {B : Finset V // Erdos1027Subsets.Splits F B} : ℝ)
```

### Pins and outstanding review

Proof repository: [https://github.com/cronrpc/erdos1027-lean](https://github.com/cronrpc/erdos1027-lean). Proof commit: `0f0f63749b77195cbd6c1b7f7ef2b11c777663c6`. Toolchain: `leanprover/lean4:v4.19.0`. Library: mathlib commit [`c44e0c8ee63ca166450922a373c7409c5d26b00b`](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b); transitive dependencies are pinned in [lake-manifest.json](https://github.com/cronrpc/erdos1027-lean/blob/0f0f63749b77195cbd6c1b7f7ef2b11c777663c6/lake-manifest.json).

No claim is made that the toolchain or library meets any current minimum safe-version policy. No curator has signed this proposal, no independent verifier is named, no checker conclusion or isolated-build environment is attested, and no award decision or recipient confirmation is recorded. The current upstream [statement schema](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/data/schema/statement.schema.json) requires at least two signatories; the record guide also requires published reviews for custom definitions. Those requirements must be fulfilled by actual authorized reviewers, after which maintainers may issue an active `statement.yaml` and enable the structured formal reference. Until then `verification.formal` and `verification/record.yaml` remain null.
