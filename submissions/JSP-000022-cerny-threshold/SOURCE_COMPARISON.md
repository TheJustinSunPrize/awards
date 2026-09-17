# Prior-source comparison

Checked on 2026-09-17. This records a bounded public-source search, not a global
novelty certificate or an independent verification of third-party proofs.

## Sources actually read

- The [Synchronizing word](https://en.wikipedia.org/wiki/Synchronizing_word)
  page, including the distinction between the Černý conjecture and its
  classical sharp family.
- Narad Rampersad's [Černý lecture slides](https://nrampers.faculty.uwinnipeg.ca/cerny.pdf),
  slides 8–9, visually inspected. These give the general construction and the
  standard reset word, with the two letters named in the opposite order. Those
  two pages do not prove the lower bound for arbitrary words.
- The [Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/Wikipedia/CernyConjecture.lean).
  Its general conjecture and the stated Shitov bound are marked `sorry`; neither
  is a proved dependency of the present project.
- The [paulklemstine/Lean Sharpness source](https://github.com/paulklemstine/Lean/blob/6653e4e473143c1bef1fbeccfef91918a9628265/Catalog/Applications/DoppelgangerPhaseLock/Sharpness.lean),
  at the fixed commit shown in the link. It uses a three-state `cerny3`
  automaton to study a topological property of synchronization of infinite
  input streams. It does not supply the minimum reset-word length for all
  state counts proved here.

Černý's 1964 [original paper](https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf)
is the mathematical attribution. Its Slovak text was not read in full in this
work, so no line-by-line derivation from that article is claimed.

## Search scope and results

The following actual GitHub API queries were performed:

| Query | Reported matches |
| --- | ---: |
| Issues: `repo:TheJustinSunPrize/awards "JSP-000022"` | 0 |
| Code: `"Cerny" extension:lean` | 12 |
| Code: `"Černý" extension:lean` | 11 |
| Code: `"Cerny" "length" extension:lean` | 5 |

Some matches were copied paths or conjecture statements. Searches can miss
equivalent results, alternative spellings, private work, and unindexed sources.
The counts and issue status are time-sensitive. They do not prove priority.

## Exact contribution and limitation

The present contribution is a from-source Lean proof of the all-state-count
sharp family, including an arbitrary-word lower bound, an explicit matching
reset word, and a final existential theorem over actual `DFA Bool (Fin N)`
objects for every `N >= 2`. The lower bound uses trajectory residues and a
progress inequality, without assuming a normal form for the word.

No code from the above candidate-specific files is imported. Standard Mathlib
definitions, lemmas and tactics are dependencies. Mathematical novelty is not
claimed. This is a classical partial result associated with JSP-000022, not a
proof of its open universal conjecture; award eligibility and attribution remain
for the prize reviewers to decide.
