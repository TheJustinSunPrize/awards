# JSP-000924: known fourth-power Sierpinski family

## Contribution and scope

This submission requests review of a complete Lean formalization of the explicit
fourth-power family in Filaseta--Finch--Kozek (2008), Section 2, using Izotov's
partial-cover and algebraic-factorization method.

For every natural number j, define

```
t_j = 734110615000775 + 36893488147419103230*j
K_j = t_j^4.
```

The source proves that K_j is positive and odd and that K_j*2^n+1 has a proper
natural-number divisor for EVERY natural exponent n, including n=0. It also
proves that infinitely many distinct fourth-power Sierpinski numbers exist.

**This is a known-result formalization, not a solution of the original no-finite-
prime-cover problem.** The last theorem rules out ONLY the particular list
{3,5,17,257,65537,641,6700417}, by examining n=2. Failure of this one list is NOT
failure of all finite lists. Neither global priority nor a new mathematical
discovery, award, or payment entitlement is asserted.

## Exact declarations

- `family_proper_divisor j n`: a divisor d with 1<d<K_j*2^n+1.
- `family_sierpinski j`: positive, odd, and nonprime values at all exponents.
- `candidate_sierpinski`: the concrete j=0 fourth power.
- `infinitely_many_fourth_powers`: a genuinely infinite subset of the naturals.
- `standard_list_not_cover j`: failure of the specified seven-prime list.
- `sophie_germain_proper_divisor`: the general algebraic factorization lemma.

The locally defined `Sierpinski` predicate uses ordinary `Nat.Prime`, `Odd`, and
the standard natural operations. Its positivity and nonprimality conditions,
together with the proper-divisor theorem, ensure actual compositeness; values
zero or one are not being treated as composite counterexamples.

## Mathematical correspondence

The progression modulus is 2*3*5*17*257*65537*641*6700417. For n not congruent to 2
modulo 4, six fixed divisors cover the remaining exponent classes:

| Exponent condition | Divisor |
| --- | ---: |
| n=1 mod 2 | 3 |
| n=4 mod 8 | 17 |
| n=8 mod 16 | 257 |
| n=16 mod 32 | 65537 |
| n=32 mod 64 | 641 |
| n=0 mod 64 | 6700417 |

The exact 64-residue certificate is proved with kernel `decide`. A universal
modular-power periodicity proof lifts it to every natural exponent, and a
congruence argument lifts the seed to every progression parameter. Proper-divisor
bounds are proved separately; divisibility alone is not treated as compositeness.

For n=4q+2, x=t_j*2^q is at least two and

```
K_j*2^n+1 = 4*x^4+1 = (2*x^2-2*x+1)*(2*x^2+2*x+1).
```

Lean checks the identity, the natural-subtraction side condition, and both
nontriviality/proper-divisor bounds. Infinitude follows by exhibiting a member
larger than every prescribed natural bound, not by checking finitely many j.

The 1995 paper and the later explicit progression interchange the roles of 641
and 6700417. Our constants and exponent classes follow the 2008 progression, whose
residues were checked against the author's preprint on printed page 6.

## Attribution and overlap

Izotov (1995) retains credit for the method; Filaseta, Finch and Kozek (2008) retain
credit for the explicit progression. Mathlib infrastructure remains credited to
its contributors. The code is independently written with OpenAI ChatGPT
assistance under the submitting account's direction.

HowieHwong's earlier Lean proof already establishes UNRESTRICTED infinitude using
Selfridge's 78557 family. We acknowledge that proof and make no claim to first
formalizing the unrestricted infinitude theorem. Its source is linked in
[PROVENANCE.md](PROVENANCE.md); it is not imported or redistributed here. The
present target specifies fourth powers and the different partial-cover/algebraic
construction.

Bounded searches of official issues/PRs and public Lean code did not locate an
earlier implementation of this exact family. Search indexing and unpublished
work remain limitations; priority is a reviewer question.

## Reproduction and review

The committed toolchain and dependency manifest are required. From this directory:

```sh
sha256sum -c SOURCE_SHA256SUMS
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

See [VERIFICATION.md](VERIFICATION.md) for source pins, actual results, archive
hashes, and remaining verification boundaries. Contributor-run CI and two checker
implementations do not constitute independent human or organizer certification.

Proposed recipient placeholder: `RECIPIENT-JSP-000924-KZ-A`, confirmation pending.
Please assess statement fidelity, the incremental formalization, overlap,
appropriate intake placement, and contribution eligibility. No catalog flags,
candidate/award records, recipient profiles, schemas, validators, or tests are
changed. The original no-finite-cover question and the general simultaneous-powers
theorem for every R remain outside this package.
