# JSP-000400: Lean formalization of the sum-of-two-squares approximation theorem

## English

Grigory A. Margulis proved the mathematical result. This submission supplies its Lean formalization: for every positive irrational real alpha and every epsilon > 0, there are strictly positive natural numbers x, y and z satisfying |x^2+y^2-alpha*z^2| < epsilon. It also proves |alpha*(x^2+y^2)-z^2| < epsilon and arbitrarily large denominators.

The [complete Lean project](../../../proofs/jsp-000400/README.md) accompanies this candidate. The [statement and evidence guide](../../../proofs/jsp-000400/SUBMISSION.md) identifies the original question, fixed sources, theorem declarations and reproduction results. The dedicated Lean workflow compiles the actual proof, checks its modules and audits theorem axioms.

The candidate is submitted for designated verification. The formal record is pending the repository's authorized review and statement signatures; the supplied build evidence is recorded separately in the proof project.
