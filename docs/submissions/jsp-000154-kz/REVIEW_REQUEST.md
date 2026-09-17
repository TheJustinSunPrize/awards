# Review request: JSP-000154 elementary Sidon lower bound

Please assess this scoped formalization contribution for JSP-000154 / Erdős Problem 156. The open O(N^(1/3)) existence question is not solved. The organizer catalog's Open / Lean No / Eligible No flags are preserved. This submission requests contribution review and does not establish a right to any prize.

## English

The package proves, for every natural N and every inclusion-maximal Sidon subset of {1,...,N} of size m, the universal inequality 2*N <= m^3+m. It also proves N^(1/3) <= m and (2*N)^(1/3) <= m+1, existence of maximal sets, attainment of the actual minimum, the same bounds for that minimum, and equivalence of the extension predicate with ordinary inclusion-maximality.

The classical elementary lower-bound direction and original problem retain mathematical credit; no original mathematical discovery, first formalization, Ruzsa upper bound or solution of the open question is claimed. See README.md for definitions, counting argument, references and attribution.

## Evidence

- [Immutable tested source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/96d378d5d0999da2bde29beb1d9f8f7c8ac2dead/projects/jsp-000154).
- [Public reproduction run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35175990969).
- [Completed public verification](PUBLIC_VERIFICATION.md) records the checks, artifact metadata and remaining review gates.

Local compilation, Lean kernel replay, nine axiom audits and the false-arithmetic negative control passed. Public CI also passed; independent NaNoda checked 17,926 declarations with no errors. Allowed axioms are propext, Classical.choice and Quot.sound.

Self-submission by GitHub account ketianzhang1-lang, prepared with OpenAI ChatGPT assistance. Proposed contributor RECIPIENT-JSP-000154-KZ-A remains unconfirmed. Please review statement fidelity, attribution, overlap, intake placement and eligibility. No candidate, award, recipient-confirmation or payment record is created.
