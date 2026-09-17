# Exact reset threshold of the Černý automata

For every integer N≥2, this project constructs a deterministic finite automaton on `Fin N` over a two-letter alphabet and proves that its shortest synchronizing word has length exactly (N−1)². This is the classical extremal family introduced by Ján Černý in 1964. It establishes sharpness of the proposed bound; it does not prove the open conjecture for arbitrary synchronizing automata.

The Lean source was written for this project. Mathematical attribution remains with Černý; no worldwide priority claim for the formalization is made.

## Automaton and synchronization

The states are 0,…,N−1. Letter a rotates every state by one modulo N. Letter b sends N−1 to 0 and leaves all other states fixed. The alphabet is `Bool`, with `true` representing a and `false` representing b. The implementation is an actual Mathlib `DFA`; its accepting states are irrelevant to synchronization and are chosen to be empty.

A word is synchronizing if there is a state q such that reading the word from every initial state ends at q. The implementation parameter `n` stands for N−2, so `automaton n` has n+2 states. The final theorem `Cerny.sharp_family` is reindexed to the conventional quantifier N≥2 and has state type `Fin N`.

## Lower bound for arbitrary words

For a word w, let A(w) be the number of rotation letters. For each initial state i, let E(w,i) count the occurrences of b that actually move that trajectory from N−1 to 0. Write q(w,i) for its final state, using the representative in {0,…,N−1}.

Three invariants hold for every word and initial state:

\[
\begin{aligned}
q(w,i)&\equiv i+A(w)+E(w,i)\pmod N,\tag{1}\\
(N-1)E(w,i)+q(w,i)&\le A(w)+i,\tag{2}\\
A(w)+E(w,i)&\le |w|.\tag{3}
\end{aligned}
\]

All three are proved by induction on the word. For (1), both a and an effective b advance the residue by one; an ineffective b changes nothing. For (2), rotation advances the integer representative by at most one. An effective b trades a representative of N−1 for zero while increasing E by one, preserving the relevant balance. For (3), each effective merge corresponds to an actual b occurrence.

Now suppose w synchronizes to q. Choose the initial state

\[
i\equiv q-A(w)+1\pmod N.
\]

Since synchronization holds from this state too, (1) implies E(w,i)≡−1 (mod N). Thus E(w,i)≥N−1. Combining (2) with i≤N−1 yields

\[
A(w)\ge (N-1)E(w,i)-(N-1)\ge(N-1)(N-2).
\]

Finally, (3) gives

\[
|w|\ge A(w)+E(w,i)\ge(N-1)^2.
\]

The proof imposes no normal-form assumption on w and does not enumerate words up to a fixed size. The modular choice of i uses `ZMod N`; the counters and the progress inequality use natural numbers. Lean's kernel checks both parts and their connection.

## Matching word

Consider

\[
w_N=b\bigl(a^{N-1}b\bigr)^{N-2}.
\]

After the initial b, every state's integer representative is at most N−2. The block a^(N−1)b acts as the natural-number predecessor on every state: positive states move down by one, and zero remains zero. After N−2 blocks all states therefore equal zero. Its length is

\[
1+N(N-2)=(N-1)^2.
\]

The boundary case N=2 is included: there are no blocks and the word is just b.

## Formal theorem map

| Lean declaration | Meaning |
| --- | --- |
| `Cerny.automaton` | Explicit DFA with n+2 states. |
| `Cerny.IsReset` | All initial states reach one common final state. |
| `Cerny.effective_le_merges` | Inequality (3). |
| `Cerny.residue_invariant` | Congruence (1). |
| `Cerny.progress_invariant` | Inequality (2). |
| `Cerny.exists_many_effective` | Synchronization forces some trajectory to undergo at least n+1 effective merges. |
| `Cerny.reset_length_lower_bound` | Every reset word has length at least (n+1)². |
| `Cerny.run_rotations` | Exact result after any number of rotation letters. |
| `Cerny.run_block_val` | One standard block acts as predecessor. |
| `Cerny.run_blocks_val` | Repeated standard blocks subtract their count, with natural truncation. |
| `Cerny.resetWord_resets` | The explicit classical word synchronizes to zero. |
| `Cerny.resetWord_length` | Its length is exactly (n+1)². |
| `Cerny.exact_reset_threshold` | A reset word of length at most L exists iff (n+1)²≤L. |
| `Cerny.sharp_family` | For every N≥2, an actual DFA on `Fin N` has exact reset threshold (N−1)². |

The last result is an attained exact threshold for an unbounded family of automata, not a finite computational check and not a universal upper bound on all automata.

## Sources and prior work

- J. Černý, *Poznámka k homogénnym experimentom s konečnými automatmi*, Matematicko-fyzikálny časopis 14 (1964), 208–216. [Original paper](https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf).
- [Synchronizing word](https://en.wikipedia.org/wiki/Synchronizing_word), for the distinction between the conjecture and the established sharp family.
- Narad Rampersad, [Černý's Conjecture](https://nrampers.faculty.uwinnipeg.ca/cerny.pdf), slides 8–9, for the classical construction and standard word, with the two letters named in the opposite order.
- [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/Wikipedia/CernyConjecture.lean). Its open conjecture is not used as a premise of this project.

The lower-bound exposition above describes the two-invariant argument implemented in this source. It is not a claim that this argument is mathematically new. Public searches also found a separate three-state Černý example used to study synchronization of infinite input streams; it does not supply the all-N minimum-length theorem asserted here. Searches are not an exhaustive proof of formalization priority.
