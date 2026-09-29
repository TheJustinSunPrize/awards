# JSP-000301: a complete counterexample to the stated question

Date: 2026-09-17.

**Answer: no.** The consecutive positive integers 12167 and 12168 are both
powerful, but neither is a perfect square. This note gives a complete,
self-contained disproof of the exact yes/no question recorded in JSP-000301.
The counterexample already appears in the catalog: this is a checked
explanation of a known result, not a new discovery.

## Selecting and checking the question

Three candidate entries were read before selecting this problem:

| Entry | Local question and selection decision |
| --- | --- |
| [JSP-000301](../problems/catalog-0301-0400.md#JSP-000301) | Asks whether consecutive powerful positive integers must include a square. Its description, explicit counterexample, and review notes make the exact scope unambiguous. Selected because every assertion needed for a complete negative answer can be proved by integer arithmetic. |
| [JSP-000307](../problems/catalog-0301-0400.md#JSP-000307) | Asks whether three consecutive integers can have strictly decreasing largest prime factors. Not selected: the entry gives literature references but no detailed scope discussion comparable to JSP-000301's explicit clarification. No result about this candidate is asserted here. |
| [JSP-000953](../problems/catalog-0901-1000.md#JSP-000953) | Asks for a representation of every sufficiently large integer as two squares minus a third, each square bounded by that integer. Not selected: a finite collection of examples would not settle its universal eventual quantifier, and a complete representation proof would require a separate argument. |

The selected entry's **Problem description** is exactly:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

Its review notes define powerful numbers by prime exponents, verify the same
counterexample, and explicitly state that the record covers **this yes/no
question only**, not the separate counting question in Erdős problem #365.
Thus the scope used here is supported by the local description and review
notes together, not inferred merely from a title. Its status already says
“Solved (disproved)”; this note does not change any catalog record.

**Source limitation.** The local entry was read in full. It cites *Powerful
numbers* (1970), *Consecutive integer pairs of powerful numbers and related
Diophantine equations* (1976), and *Unsolved problems in number theory* (2004).
External retrieval in this session failed because the configured proxy was
unreachable; a direct retry also failed with a DNS-resolution error. These
historical publications and the external Erdős page were not independently
read. The complete statement answered here is therefore the explicitly scoped
local JSP-000301 question, not an asserted reconstruction of a historical
paper or a solution to the separate counting problem. The original proposal
date, first-discovery date, and discoverer's identity are not established here.
The elementary proof below does not depend on those external sources.

## Definitions and exact quantified proposition

A positive integer p is **prime** if p > 1 and its only positive divisors are
1 and p. For positive integers d and m, the notation d | m means that
m = dq for some integer q.

A positive integer m is **powerful** if, for every prime p,

    p | m  implies  p² | m.

Equivalently, every exponent in its prime factorization is at least 2.
A **perfect square** is an integer of the form a² for an integer a ≥ 0;
allowing negative a gives exactly the same squares. The integer 1 is powerful
vacuously and is a square, but this convention does not affect the example.

Every pair of consecutive positive integers can be written uniquely in
increasing order as n, n+1 with n ≥ 1. The proposed assertion is

    For every integer n ≥ 1:
      [n is powerful and n+1 is powerful]
        implies
      [(there exists an integer a ≥ 0 with n = a²)
        or (there exists an integer b ≥ 0 with n+1 = b²)].

Its negation requires just one integer n ≥ 1 for which both antecedent
conditions hold and both alternatives in the conclusion fail. We now
establish exactly that negation, with n = 12167.

## Complete proof

First, the integers 2, 3, 13, and 23 are prime. For completeness, any composite
integer m > 1 has a divisor d with 2 ≤ d ≤ sqrt(m): in a factorization m = ab
with a,b > 1, the smaller factor cannot exceed sqrt(m). There are no such
integer candidates for 2 or 3. For 13 the only candidates are 2 and 3, neither
of which divides 13. For 23 they are 2, 3, and 4: 23 is odd, has remainder 2
upon division by 3, and is not divisible by 4. This proves the stated primality.

The following are exact arithmetic identities:

    23³ = 529 · 23 = 10580 + 1587 = 12167,
    2³ · 3² · 13² = 8 · 9 · 169 = 72 · 169 = 12168.

Both integers are positive, and 12168 − 12167 = 1, so they are consecutive.
These displayed products are complete prime factorizations. We use the
elementary prime-divisor property that a prime dividing a product divides a
factor. One justification is: if a prime p does not divide x, the Euclidean
algorithm gives integers u,v with up + vx = 1; multiplying by y shows that
p | xy implies p | y. Repeatedly applying this property to the displayed
products shows that there can be no other prime divisors.

The only prime divisor of 12167 is 23, and its square divides 12167 since
12167 = 23² · 23. Hence 12167 is powerful. The only prime divisors of 12168
are 2, 3, and 13, and their squares all divide it, with integer quotients

    12168 / 2² = 3042,
    12168 / 3² = 1352,
    12168 / 13² = 72.

Hence 12168 is powerful as well.

Finally,

    110² = 12100 < 12167 < 12168 < 12321 = 111².

Squares of nonnegative integers are strictly increasing, since
(a+1)² − a² = 2a+1 > 0 for a ≥ 0. There is no integer strictly between 110
and 111. Therefore no integer square lies strictly between 110² and 111²,
so neither 12167 nor 12168 is a perfect square.

We have a pair meeting every hypothesis and neither alternative conclusion.
The universal assertion is false, and the answer to JSP-000301 as recorded
is **no**. ∎

## Coverage of every condition and quantifier

| Original requirement | What the proof establishes |
| --- | --- |
| Positive integers | 12167 > 0 and 12168 > 0. |
| Consecutive | The second integer equals the first plus 1. |
| Both powerful, for every prime divisor | Complete prime factorizations identify all prime divisors; their exponents are 3 and (3,2,2), respectively. Each prime square divides the relevant integer. |
| At least one is a square | Both lie strictly between consecutive squares, so both existential square assertions fail. |
| “Must” for all such pairs | One pair satisfying the hypotheses and falsifying the conclusion disproves the universal implication completely. No infinite family or classification is required for a negative answer. |

No claim is made that this is the smallest counterexample. Nor does the
argument count such pairs, establish an asymptotic density, or resolve any
stronger question. Those are not parts of the selected local proposition.

## Independent arithmetic verification

Run the standard-library-only companion script from the repository root:

```sh
python3 scripts/verify_jsp_000301.py
```

The [script](../scripts/verify_jsp_000301.py) factors each number by trial
division rather than assuming the displayed factors, reconstructs the
number, tests every prime exponent, checks consecutiveness, and uses exact
integer square roots to exclude squares. It also checks the definition on
1, 8, 9, and 12 (in particular, 12 is not powerful because its factor 3 has
exponent 1). It does not use floating-point approximations, external packages,
network access, or a probabilistic test.

Expected verified output:

```text
12167: factors={23: 3}, powerful=True, isqrt=110, square=False
12168: factors={2: 3, 3: 2, 13: 2}, powerful=True, isqrt=110, square=False
PASS: consecutive powerful positive integers, neither a square
```

This computation checks a finite arithmetic certificate; the written argument
above is the complete mathematical disproof. The Python computation is not
Lean formalization or independent scholarly review. A separate
[Lean proof and evidence packet](submissions/jsp-000301/README.md) now supplies
the locally compiled formalization. Earlier repository checks were blocked
by missing PyYAML; publication checks later passed in an isolated environment.
The arithmetic script itself needs no external packages. Catalog status,
award eligibility and attribution are unchanged.
