# Scoped contribution for eligibility review

Please assess this independently written formalization of the classical
prime-multiple lower-bound construction for JSP-000476 / Erdős 587.

Revision 2 classifies every positive integer step d: writing d=b^2*a with
a squarefree, {d,2d,...,md} is square-sum-free exactly when m(m+1)<2a.
For squarefree steps, the same condition excludes every perfect-power subset
sum. For nonsquarefree steps, only square avoidance is claimed; {8} is a
verified counterexample to the stronger claim.

The retained prime-step criterion covers every prime p and every natural m:
{p,2p,...,mp} is square-sum-free if and only if m(m+1)<2p. The proof also
excludes all higher perfect-power subset sums under the same condition,
constructs a square-sum witness when it fails, and supplies an explicit
uniform size-m construction in [1,m^2(m+1)].

This is a known-result formalization with an exact construction criterion,
not a claim to the original problem's complete asymptotic solution. The
prior external Lean proof for Erdős 587 is prominently acknowledged in
README.md. There is no claim of first priority or mathematical novelty.

Mathematical attribution: Erdős for the construction, as recorded in
Nguyen–Vu, Example 1.2, *Squares in sumsets*. The deeper upper-bound theorem
belongs to Nguyen and Vu and is not re-proved here. Mathlib supplies
Bertrand's postulate and standard infrastructure.

Proposed recipient: RECIPIENT-JSP-000476-KZ-A, confirmation pending.
AI assistance: OpenAI ChatGPT.

Please review statement fidelity, attribution, overlap with existing
formalizations, substantive incremental contribution, and eligibility.
No catalog flag, candidate status, award, or payment entitlement is asserted.
The reviewer should decide whether this scoped component merits intake
before treating it as a candidate for recognition.

See STATEMENT.md and VERIFICATION.md for the precise coverage and evidence.
