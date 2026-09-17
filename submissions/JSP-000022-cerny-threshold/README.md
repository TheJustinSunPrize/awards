# Exact reset threshold of the Černý automata

For every integer `N >= 2`, this Lean 4 project constructs an actual Mathlib
`DFA Bool (Fin N)` whose shortest synchronizing word has length exactly
`(N - 1)^2`. A word synchronizes if it sends every initial state to one common
final state.

This is a complete formal proof of the classical extremal family associated
with **JSP-000022**. It establishes sharpness of the proposed Černý bound. The
universal upper bound for arbitrary synchronizing automata remains open and is
not asserted here. The underlying mathematical result is due to Ján Černý
(1964); this project makes no claim to new mathematics or global formalization
priority.

The proof covers arbitrary input words and every state count, rather than a
bounded enumeration. Three trajectory invariants give the lower bound. The
explicit word `b (a^(N-1) b)^(N-2)` attains it. The boundary case `N = 2` is
included.

## Main declarations

- `Cerny.automaton`: cyclic rotation and a letter merging the last state into 0.
- `Cerny.IsReset`: synchronization from all initial states.
- `Cerny.residue_invariant`, `progress_invariant`, `effective_le_merges`:
  the three arbitrary-word invariants.
- `Cerny.reset_length_lower_bound`: all reset words have length at least
  `(n+1)^2` for the `n+2` state family.
- `Cerny.resetWord_resets` and `resetWord_length`: the matching explicit word.
- `Cerny.exact_reset_threshold`: exact attained threshold for `automaton n`.
- `Cerny.sharp_family`: for every `N >= 2`, an actual DFA on `Fin N` has a
  reset word of length at most `L` if and only if `(N-1)^2 <= L`.

The implementation parameter `n` means `N - 2`; the last theorem uses the
conventional state count `N`. Accepting states are irrelevant to synchronization
and are set to the empty set.

## Reproduction

Lean and Mathlib: `v4.33.1`. Mathlib commit:
`0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
lake exe cache get
lake --wfail build Cerny
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker --verbose Cerny
```

The checked build and 10-declaration axiom audit are recorded in `verification/`.
On Windows, `./verify.ps1` reproduces these checks, scans the proof source for
proof escapes, replays the local module, and records source hashes and versions.
The audit reports only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`), with no `sorryAx` or problem-specific axiom. `leanchecker` replays
the local module using the same Lean kernel implementation, while trusting
imported dependency caches; it is not an independently implemented checker or a
fresh replay of every Mathlib dependency.

The local workspace reuses a dependency-cache junction. `.lake` and the junction
are not part of the source deliverable. A fresh checkout obtains the pinned
dependencies from the manifest.

See `PROOF.md` for the full mathematical argument and theorem map, and
`SOURCE_COMPARISON.md` for the precise scope of the prior-source search.

## Sources and attribution

- J. Černý, *Poznámka k homogénnym experimentom s konečnými automatmi*,
  Matematicko-fyzikálny časopis 14 (1964), 208–216.
  [Original paper](https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf).
- [Synchronizing word](https://en.wikipedia.org/wiki/Synchronizing_word).
- Narad Rampersad, [Černý's Conjecture](https://nrampers.faculty.uwinnipeg.ca/cerny.pdf),
  slides 8–9, for the family and standard synchronizing word.
- [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/Wikipedia/CernyConjecture.lean).

These sources identify the classical result and the open general conjecture.
No unproved conjecture is imported as an assumption of this project.

The project source is released under the Apache License 2.0; see `LICENSE`.
