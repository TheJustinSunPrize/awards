# Statement match and mathematical scope

The reference is Erdős 302, as encoded in formal-conjectures commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Its question asks for the asymptotic
maximum f(N), and separately whether its density tends to 1/2.

| Reference or required meaning | Formal declaration or treatment |
| --- | --- |
| Finite subset of positive integers bounded by N | `A ⊆ Finset.Icc 1 N`; all denominators are positive. |
| No distinct a,b,c satisfying 1/a = 1/b + 1/c | `NoUnitFractionTriple`; equality is in the rational numbers and the three distinctness hypotheses are retained. |
| Maximum cardinality f(N) | `IsMaxNoTripleCard`; the same `IsGreatest` definition as upstream. |
| Existence of a maximum | `JSP000254.extremalCount_isMax`, proved for every N from the finite powerset. |
| Explicit lower bound at every N | `JSP000254.finite_lower_bound`: an admissible set of exactly 5 floor(N/8) elements. |
| Cambie's asymptotic lower bound | `Erdos302.erdos_302.variants.lower_five_eighths`: for every epsilon > 0, eventually f(N) >= (5/8 - epsilon)N. |
| Negative answer to the one-half subquestion | `Erdos302.erdos_302.parts.ii`: the density does not tend to 1/2. |
| Concrete, unconditional instance | `JSP000254.extremal_not_tendsto_half`, applied to the proved extremal function. |
| Optimal density, existence of a limit, nine-tenths upper bound | Not claimed. |

The two declarations in namespace `Erdos302` use exact copies of the upstream
mathematical definitions and the same theorem types. The new proof is in
namespace `JSP000254`; the final declarations bridge by definitional equality.
No file containing the upstream admitted theorems is imported.

## Proof outline

For a natural number t, take the odd integers below 2t and the upper interval
{4t+1,...,8t}. The two sets are disjoint and have t and 4t elements respectively.
If a unit-fraction equation held, clearing positive denominators gives ab+ac=bc,
with a<b and a<c. When a>4t, the bounds b,c<=8t<2a give a contradiction.
When a<2t is odd, another odd denominator contradicts parity of that equation.
If both other denominators exceed 4t, they exceed 2a and again contradict the
equation. All cases are covered. Taking t=floor(N/8) gives the finite bound.

The estimate f(N)>=5N/8-5 gives the asserted asymptotic bound. Were f(N)/N to
tend to 1/2, it would eventually be strictly below 9/16. The lower bound with
epsilon=1/16 says it is eventually at least 9/16, a contradiction.

At N=0 the constructed set is empty, and the finite bound still holds. All division
by N used for the limit contradiction occurs only after the explicit condition N>=1.
