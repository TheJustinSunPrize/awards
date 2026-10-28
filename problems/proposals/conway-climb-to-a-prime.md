# Proposed entry: Conway's Climb to a Prime

This is a problem-inclusion and complete-formalization proposal associated
with [issue #701](https://github.com/TheJustinSunPrize/awards/issues/701).
The catalog identifier is unassigned. This proposal is not an accepted
catalog entry, a public candidate record, a verification decision, or an
award announcement. Maintainers are asked to decide whether to include the
problem and where to place its catalog record.

## Original problem and complete mathematical resolution

For an integer n >= 2, write its canonical prime factorization with distinct
prime bases in increasing order. Omit every exponent equal to one. Move the
other exponents onto the baseline immediately after their corresponding
prime and concatenate the decimal representations to define f(n).
Conway's conjecture asserted that iteration eventually reaches a prime
for every starting value. The related OEIS formulation also permits
eventual arrival at one.

The original statement is problem 5 in John H. Conway's
[Five $1,000 Problems, updated 2017](https://oeis.org/A248380/a248380.pdf).
The transformation and iteration are recorded in
[OEIS A080670](https://oeis.org/A080670) and
[OEIS A195264](https://oeis.org/A195264).

James Davis disproved the universal conjecture in 2017 with the composite
fixed point

    13532385396179 = 13 * 53^2 * 3853 * 96179.

Flattening this factorization gives the same integer. Every finite iterate
therefore remains composite and is not one. This single counterexample
completely refutes both universal formulations; the result does not claim
to classify the trajectories of every starting value.

Mathematical discovery is attributed to Davis, as recorded in the original
document's June 8, 2017 postscript, the OEIS record, and
[Davis's June 9, 2017 account](https://mathoverflow.net/a/271804).
The original document reports that Davis claimed Conway's historical
$1,000 bounty. This proposal does not seek that historical bounty.

## Pinned Lean formalization

| Field | Submitted evidence |
| --- | --- |
| Public repository | [aichiwuhuarou/conway-climb-lean](https://github.com/aichiwuhuarou/conway-climb-lean) |
| Branch | `main` |
| Proof commit | `7d192a6ecab11b8ed328b090e41d376d97782d2d` |
| Main source | [ConwayClimb/Counterexample.lean](https://github.com/aichiwuhuarou/conway-climb-lean/blob/7d192a6ecab11b8ed328b090e41d376d97782d2d/ConwayClimb/Counterexample.lean) |
| Main declarations | `ConwayClimb.exists_counterexample`, `ConwayClimb.not_climbToPrime`, `ConwayClimb.not_climbToOneOrPrime` |
| Toolchain | Lean `4.33.1` |
| Mathlib revision | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Instructions and attribution | [README at the proof commit](https://github.com/aichiwuhuarou/conway-climb-lean/blob/7d192a6ecab11b8ed328b090e41d376d97782d2d/README.md) |

The source defines the transformation for arbitrary natural-number inputs
using their prime factorizations, proves the displayed fixed point, and
proves that all its finite iterates are neither prime nor one. Thus the
formalization addresses the original universal claim through a complete
refutation, rather than merely checking a bounded orbit.

The submitter account is [aichiwuhuarou](https://github.com/aichiwuhuarou).
The new contribution offered for review is the 2026 Lean formalization,
with AI assistance disclosed in the source repository. This is a
self-recommendation with a direct interest in formalization attribution
and any potential award. It makes no claim to Davis's mathematical
discovery, absolute first-formalizer priority, or confirmed recipient status.

## Reproduction and verification evidence

At the pinned source version, the documented commands are:

```text
lake exe cache get
lake --wfail build
lake env lean ConwayClimb/Counterexample.lean
lake env lean Audit.lean
lake env leanchecker --fresh --verbose ConwayClimb
```

The public [GitHub Actions verification run](https://github.com/aichiwuhuarou/conway-climb-lean/actions/runs/35221059769)
completed successfully on Ubuntu for the exact proof commit above. Its
workflow performs a warning-free build, the direct Lean invocation,
ten-declaration axiom audit, and fresh Lean kernel replay. The pinned
repository also retains local verification evidence.

The reported audited axiom closures contain only `propext`,
`Classical.choice`, and `Quot.sound`. The proof does not use `sorry`,
`admit`, a custom unproved mathematical axiom, or `native_decide`.
The replay uses Lean's own kernel, not a separately implemented proof
checker. The AI-assisted statement comparison and successful CI are not
external peer verification or a Prize verification decision. Official
review must still verify statement fidelity, attribution, and completeness.

## Requested maintainer decisions

1. Decide whether to include this previously solved problem and its new
   complete Lean formalization, and assign the catalog identifier if accepted.
2. Confirm whether this 2026 formalization is eligible under the current
   rules despite the mathematical counterexample dating to 2017 and the
   formalization preceding catalog inclusion.
3. Confirm the appropriate formal submission and award-review route, and
   the applicable allocation provision, as requested in issue #701.

The [selection rules](https://www.hejustinsun.com/prize/rules),
[FAQ](https://www.hejustinsun.com/prize/faq), and
[open letter](https://www.hejustinsun.com/prize/letter) are referenced for
maintainer clarification. No amount or allocation is asserted here.

The current [external-submission instructions](../../CONTRIBUTING.md#external-solver-and-lean-submissions)
normally require updating an existing catalog entry. Because this problem
has no such entry, this isolated proposal explicitly requests inclusion
and placement first. It supplies public references and catalog-ready
evidence without assigning a JSP identifier, modifying screening or claim
flags, or adding proof source, dependencies, binaries, or archives.
