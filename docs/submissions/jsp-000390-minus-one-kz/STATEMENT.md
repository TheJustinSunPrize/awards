# Statement correspondence: k = -1 only

## Original question and retained scope

Erdős 479 / JSP-000390 asks about infinitely many positive integer moduli for
prescribed integer residues in the congruence 2^n = k (mod n), with k != 1.
This package fixes k = -1. It does not quantify over or settle the other residues.
The special case is already known mathematically. A new formalization of a known
special case is not claimed to improve a mathematical bound or solve an open case.

## Definitions and endpoints

`JSP000390.Solutions k` is the subset of natural numbers n for which
`0 < n` and `Int.ModEq (n : Int) ((2 : Int)^n) k` both hold. The integer
cast embeds the natural modulus without changing its value. Mathlib's standard
`Int.ModEq` is used directly; no custom primality, divisibility, infinitude or
congruence predicates change the original meaning.

- `three_pow_succ_dvd r` proves `3^(r+1) | 2^(3^r)+1` in the integers.
- `three_pow_is_solution r` yields the desired congruence modulo `3^r`.
- `minus_one_unbounded B` gives a modulus above B and above 1.
- `minus_one_infinite` proves `(Solutions (-1)).Infinite`, retaining positivity.
- `minus_one_infinite_unrestricted` is the corresponding set-infinitude statement
  without positivity, following by inclusion. This matches the k=-1 instance of
  the set expression in the general Formal Conjectures formulation, not its
  universal quantification over k.

## Mathematical proof

1. If d divides x+1 and 3 divides x+1, then 3d divides x^3+1. Write x+1=3b
   and use x^3+1=(x+1)(x^2-x+1) and x^2-x+1=3(3b^2-3b+1).
2. Start with 3 dividing 2^1+1. Induction and the cubic lifting step prove
   3^(r+1) divides 2^(3^r)+1 for every r >= 0.
3. Drop one factor of 3 and translate divisibility into Int.ModEq. Thus each
   positive natural number 3^r belongs to Solutions(-1).
4. Induction proves r < 3^r. Given a bound B, take n=3^(B+1); then n>B and n>1.
5. A set with a member above every natural bound is not bounded above and hence
   cannot be finite. This final argument, including infinitude, is checked in Lean.

No numerical finite search is used as a substitute for the infinitude proof.
No classification of all solutions is claimed.

## Review limits

This mapping and the automated evidence are prepared by the submitting contributor
with AI assistance. They are not authorized curator signatures or independent
human statement review. The prize operator must separately assess whether this
small known special case is eligible for formalization-contribution consideration.
