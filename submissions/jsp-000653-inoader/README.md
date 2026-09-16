# JSP-000653: a finite counterexample to the additional exact formula

This submission supplies formal evidence for **one explicit secondary conjecture**
in [Erdős Problem 795](https://www.erdosproblems.com/795), corresponding to
JSP-000653. It does not claim a new solution of the separate asymptotic upper-bound
question, or priority over earlier mathematical work.

Let `g(N)` be the largest size of a subset of `{1,...,N}` with all subset products
distinct. Let `F(k)` be the largest size of a subset of `{1,...,k}` with all subset
sums distinct. The additional exact formula predicts

`g(N) = sum_{k >= 1, F(k) > F(k-1)} pi(N^(1/k))`.

At `N = 48` the right side is `15 + 3 + 1 = 19`, whereas the following set has
20 elements and 1,048,576 distinct subset products:

`{5,6,7,11,13,16,17,19,23,25,27,29,31,32,36,37,41,43,47,48}`.

The main theorem is `JSP653.exact_formula_false`. A separate theorem,
`JSP653.witness_arbitrary_subsets`, proves injectivity for arbitrary subset
characteristic functions. The certificate is not limited to a sampled test set.

## Reproduce

Install the official Lean toolchain specified in `lean-toolchain` (Lean 4.34.0).
There are no external Lake dependencies. Python uses only its standard library.

```sh
lake build
lake env lean Audit.lean
lake env leanchecker --fresh --verbose JSP653
python3 scripts/check_witness.py
```

Or run `python3 scripts/verify.py` with this toolchain on `PATH`.
The script writes dated logs and source hashes to `verification/`.

The main theorem's axiom dependencies are `propext` and `Quot.sound`.
All finite certificates use kernel-checked `decide`; there is no `sorry`,
`native_decide`, or added axiom. Fresh `leanchecker` replay uses the same Lean
kernel, not an independently implemented checker. Python independently enumerates
all 2^20 products and is only a cross-check, not a premise of the Lean proof.

## Scope and award request

We request formal-evidence review and a determination of whether this separately
specified secondary-conjecture formalization can be considered under the prize's
completion-status and formalization provisions. No award, amount, accepted
candidate status, first-priority status, or eligibility is asserted.

The mathematical falsity of the formula was already known from Raghavan's work.
A public Lean proof of the **asymptotic upper bound** also predates this submission;
see `ATTRIBUTION.md`. This submission must not replace its attribution or be
treated as a first complete formalization of all of Problem 795. Please reject or
redirect this application if the same formalized secondary conclusion has earlier
qualifying evidence, or if it is not independently eligible.

Recipient placeholder: `RECIPIENT-JSP-000653-A`, pending identity confirmation.
Public submission account: `inoader`. No payment or identity information is included.

See `STATEMENT.md` for the definition-to-statement correspondence and
`ATTRIBUTION.md` for prior work and the bounded priority search.
