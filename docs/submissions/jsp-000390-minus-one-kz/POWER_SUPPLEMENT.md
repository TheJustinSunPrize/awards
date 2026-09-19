# Power-family extension: scope, proof and verification

## English

This is contributor-produced evidence supplementing PR #260. It extends the known
k=-1 case to the full known k=2^i family, for every i >= 1. It does not replace the
historical verification receipt or claim that the original all-k problem is solved.

## Exact statements

The principal new declaration is:

```lean
theorem JSP000390Power.powers_of_two_infinite (i : Nat) (hi : 0 < i) :
    (JSP000390.Solutions ((2 : Int) ^ i)).Infinite
```

Here the unchanged `JSP000390.Solutions k` is the set of **positive natural n** with
`(2 : Int)^n` congruent to k modulo n using Mathlib `Int.ModEq`. Thus the assertion
is `for every positive i, infinitely many positive n`; it does not restrict i to a
finite tested range. The unrestricted-set adapter and a combined theorem with the
old k=-1 result are also proved. No unfinished Formal Conjectures theorem is imported.

The proved general-base theorem `JSP000390Power.power_residue_infinite` is:

```lean
forall (a : Int) (i : Nat), 0 < i ->
  {n : Nat | 0 < n /\ a ^ n ≡ a ^ i [ZMOD (n : Int)]}.Infinite
```

This holds for every integer a, without a coprimality or sign assumption. It is a
supporting mathematical generalization, not a claim to new discovery or resolution
of any new prize problem. Substituting a=2 recovers the desired family. The proof also
provides a modulus greater than every prescribed natural bound.

## Mathematical attribution and proof route

The known family is credited to Graham, D. H. Lehmer and E. Lehmer in the catalog.
Quanyu Tang gives an expository proof in Section 3 / Theorem 3.1 of
[A Note on Erdos Problem 479](https://github.com/QuanyuTang/Erdos-Problem-479-Note/blob/7bd6cccea4b2ad023a334ff78bf4bef0b3366a0d/A_note_on_Erdos_Problem_479.tex).
The note explicitly does not claim new number-theoretic results. The construction
n=i*p is retained, but the new implementation replaces its prime-factor/multiplicative-
order bookkeeping with eventual periodicity in the finite multiplicative monoid ZMod i.

1. Among a^0,...,a^i modulo i, pigeonhole gives two equal powers with exponents u<v<=i.
2. Their positive difference d=v-u is a period from exponent i onward, even when a is
   not invertible modulo i. `power_tail_periodic` and `exists_zmod_power_period` prove this.
3. Choose a prime p>max(B,i) with p congruent to 1 modulo d. The implementation uses
   Mathlib's elementary `Nat.exists_prime_gt_modEq_one`, based on cyclotomic polynomials,
   not an assumed Dirichlet theorem. Its Mathlib formalization is credited to Riccardo Brasca.
4. Periodicity gives a^(i*p)=a^i modulo i. Fermat gives the equality modulo p.
5. Since p>i>0, gcd(i,p)=1, so the two congruences combine modulo n=i*p. Then n>B.

Standard finite-field, pigeonhole and integer-congruence infrastructure remains
credited to Mathlib and its contributors. OpenAI ChatGPT assisted construction and
checking under the submitting account's direction. No third-party Lean solution code
is copied into the added module. Reused Mathlib results are not claimed as our own.

The prior [rjwalters/lean-genius file](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos479Problem.lean)
proves k=2, but its general power-of-two assertion is an axiom, not a proof. It is not
imported, and its already-proved case is not reclaimed as a first formalization.
Bounded searches in the official issue/PR listings found only #260 for this topic at
preparation time. Index coverage and unpublished work remain unknown; global priority
and eligibility are not presumed.

## Exact verified source and observed checks

Source: `ketianzhang1-lang/jsp-000301-lean` at
`7f76545c7ae6a34dcd5b63455012cec87b08223b`, `projects/jsp-000390-minus-one`.
Run: [35142890158](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35142890158),
workflow run 2, job `104951536069`, completed successfully on 2026-09-16.

- `lake build --wfail`: passed, **2,872 jobs**, compiling both project modules.
- `lake env leanchecker JSP000390` and `lake env leanchecker JSP000390Power`: passed.
  This is the same kernel implementation as Lean, not a separate implementation.
- All **twelve** explicitly audited declarations (five old and seven new) depend only
  on `propext`, `Classical.choice`, and/or `Quot.sound`. The seven new reports are in
  [power-evidence/power-axioms.log](power-evidence/power-axioms.log).
- A deliberately false proposition `1=0` was rejected. It is a pipeline sanity check,
  not an exhaustive checker soundness test.
- NaNoda 0.4.17, exact commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, reported:

```text
Checked 24448 declarations with no errors
```

The exporter `leanprover/lean4export@6cea97789dc088ea47fcea15692db85685aedac5` was built
with the same Lean 4.34.0 toolchain. Requested targets include the general-base theorem
and the combined family theorem; all their transitive dependencies are exported.
Strict allowlist: `[propext, Classical.choice, Quot.sound]`, with
`unpermitted_axiom_hard_error: true`. No compiler-trust or native-evaluation axiom is
allowed. Pretty-printed target statements and the positive-modulus predicate are
included in [power-evidence/power-nanoda-statements.txt](power-evidence/power-nanoda-statements.txt).

All proof, audit and project-configuration bytes in this supplement match the source
archive from that run; reproduction scripts remain in the exact pinned source project. The Mathlib commit remains
`5ed2965256430c3649e86755f9576b54eca72435`; all nine dependency revisions are locked.
The original k=-1 source and audit are byte-for-byte unchanged from the initial submission.

## Full evidence archive

[GitHub artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35142890158/artifacts/10465807742)
`jsp-000390-power-family-evidence`, artifact ID **10465807742**.

| Item | Bytes | SHA-256 |
| --- | ---: | --- |
| Artifact ZIP | 18676770 | b43b0ce25fad347d55c8cb6bb09709ef8e7f794fbac4ad33eef5e7b1f07f51a4 |
| Included source.tar.gz | 10136 | 7062ec3f609e1bdb867a22819d626067c38c9dbc3036432a6685203aa6824d0d |
| power-export.ndjson.gz | 18667132 | 0fd5a087a02845f0cd3967016a9591538a049f38696aa285f9db16896b9bc12d |

The downloaded ZIP hash, the source archive, and copied source bytes were checked
before this receipt was prepared. GitHub reports expiration on **2026-12-15**; this
is finite-retention evidence, not independent permanent archival. Compact actual logs
are also included here. The independent finite Python cross-check used during development
is not a proof dependency and is not substituted for the quantified Lean theorem.

## Remaining review boundaries

Both checking implementations were run by the submitting contributor. Official cached
Mathlib and network access were used. The result is not an independently signed human
review, a fresh offline rebuild of all dependencies, an organizer minimum-safe-version
approval, an award decision, or permission to pay. Historical mathematical credits and
existing k=2 formalization are retained. The original arbitrary-k problem, any award
eligibility for the combined known-family formalization, amount and priority remain
for substantive review. No separate reward is requested for each i or the general-base lemma.
