# Statement and source review

Reviewed on 2026-09-17 by a separate Codex agent from the proof author. This is
an AI source-level mathematical and specification review. It is not a second
kernel, an independent checker implementation, a human peer review, or a claim
of new mathematics. No proof source was changed during this review.

Reviewed file: `Cerny.lean`, all 234 lines as present at review time.
SHA-256: `02675b9d0244a1b1574b136078624544f8b31f73c7481cb7e0cbe1f574e4bd5e`.
Build, axiom-audit, and kernel-replay evidence are separate from this document.

## Result

No statement mismatch or mathematical gap was identified in the reviewed
source. The final theorem constructs, for every actual state count `N >= 2`, a
Mathlib `DFA Bool (Fin N)` whose least reset-word length is exactly `(N-1)^2`.
The source establishes the classical extremal family. It does not establish the
conjectured upper bound for arbitrary synchronizing automata.

## Automaton and reset semantics

`State n` is `Fin (n+2)` (line 17), so the auxiliary parameter is two less than
the actual state count. The `true` transition is the cyclic successor modulo
`n+2`; `false` maps the last state `n+1` to zero and fixes all other states
(lines 19-28). These are the conventional two transitions of the Cerny family,
up to letter naming and state labels.

`run` is directly Mathlib's `DFA.evalFrom`, with no independent or simplified
transition semantics (line 30). `IsReset` says that one common final state is
reached from every initial state (line 32). The fixed `start` and empty `accept`
set of the DFA are irrelevant to this all-initial-states reset property; they do
not make the reset claim vacuous. `run_append` uses the Mathlib append law and
executes the left subword first (line 55).

## Lower bound for arbitrary words

Every lower-bound lemma quantifies over an arbitrary `List Bool`. No restriction
to alternating words, reduced words, or the displayed candidate reset word is
assumed. Write `m=n+2`, let `r` be the number of rotation letters, and let `e_i`
be the number of merge letters that actually move the trajectory from state i.

1. `effective_le_merges` (line 60) proves `r+e_i <= |w|`. The recursive counter
   follows the updated state after each transition, so an effective merge is
   counted only when that particular trajectory was at state `m-1`.
2. `residue_invariant` (line 74) proves `final_i = i+r+e_i` in `ZMod m`. A
   rotation advances by one residue; an effective merge from `m-1` to zero also
   advances by one residue; all other merge transitions fix the state.
3. If the word resets to q, `exists_many_effective` (line 116) selects the initial
   state represented by `q-r+1` in `ZMod m`. `ZMod.val_lt` makes this an actual
   element of `Fin m`, and `natCast_zmod_val` gives the intended residue. After
   substitution, the residue invariant gives `e_i = -1` in `ZMod m`.
   Consequently `e_i % m = m-1`; `Nat.mod_le` gives `e_i >= m-1`. Here `m>=2`
   follows from its definition, so the value-of-negative-one calculation has no
   zero-modulus or one-state exception.
4. `progress_invariant` (line 96) proves `(m-1)e_i + final_i <= r+i`. An
   effective merge drops the integer state from `m-1` to zero. A nonwrapping
   rotation increases it by one, and a wrapping rotation can only improve the
   inequality. This is an inequality on ordinary naturals, not a mistaken
   inequality between residues.
5. For the selected trajectory, `i <= m-1` and `final_i >= 0`, whence
   `r >= (m-1)e_i-(m-1)`. Combining the preceding facts yields
   `|w| >= r+e_i >= m*e_i-(m-1) >= (m-1)^2`. This is exactly the argument of
   `reset_length_lower_bound` (line 136).

The selected initial state may depend on the whole word and the common reset
state; the existential claim allows this. The proof does not need all initial
trajectories to incur the same number of effective merges.

## Explicit attaining word

One `block n` is `n+1=m-1` rotations followed by a merge (line 157).
`run_block_val` proves that it takes each integer state value x to `x-1`, using
natural subtraction, hence fixing zero and decrementing positive states
(line 159). `run_blocks_val` iterates this saturation-at-zero map (line 181).

The candidate word is `false :: blocks n n`, namely
`b (a^(m-1) b)^(m-2)` (line 198). The initial merge puts every state in the
range `0,...,m-2`; the following `m-2` blocks take every state to zero. Its
length is `1 + m*(m-2) = (m-1)^2`, proved by `resetWord_resets` and
`resetWord_length` (lines 200 and 210). The boundary case `n=0`, actual state
count two, is included: the word is the single merge letter and has length one.

## Final quantifiers and state count

`exact_reset_threshold` (line 215) proves an equivalence for every budget L:
a reset word of length at most L exists if and only if `(n+1)^2 <= L`.
It combines the universal lower bound with the explicit witness, rather than
claiming exactness from one constructed word alone.

`sharp_family` (line 226) accepts an arbitrary `N` with `2 <= N` and obtains
`N=n+2`. Its existential object has the exposed type `DFA Bool (Fin N)`, and its
reset predicate is expanded in terms of `M.evalFrom`. Thus the auxiliary
parameter change does produce all actual state counts at least two, with no
shifted-index ambiguity. The right side is `(N-1)^2`, not the threshold for an
automaton of a different size.

The imports, the definitions, and the theorem bodies were also inspected for a
trivializing hypothesis, `sorry`, a custom axiom, and compiler-trust proof
shortcuts; none was found in this file. This source inspection does not replace
the separate strict build and transitive axiom audit.
