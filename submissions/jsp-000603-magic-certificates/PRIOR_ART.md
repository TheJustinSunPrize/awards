# Sources and prior-work check

## Original mathematics

Eyal Ackerman, Kevin Buchin, Christian Knauer, Rom Pinchasi and Günter Rote,
*There are not too many magic configurations*, Discrete & Computational Geometry
39 (2008), 3–16. The original geometric classification is theirs.

- [Author-hosted 2007 preprint](https://math.haifa.ac.il/ackerman/publications/magic-socg07.pdf),
  especially the final “Weakly magic configurations” discussion on PDF page 11.
- [TOPP problem 65](https://topp.openproblem.net/p65), recording the history and solution.
- [Erdős 735](https://www.erdosproblems.com/735), matching the catalog question.

The degree-based formula and uniqueness are **known mathematics**, not discoveries
claimed by this submission. The proof source here is a new Lean implementation of
that argument, with a checked all-cases certificate, a geometry bridge and
rational/real equivalence. No text of the paper is redistributed.

## Existing public Lean work

The search found the `rjwalters/lean-genius` work on Erdős 735 and its higher-flat
extensions. It must not be described as an untouched subject with no Lean work.
At the fixed source below, the parent file declares `magic_classification` as an
axiom and contains other axiomatized results. We inspected the source rather than
relying on a “solved” presentation label:

- [Pinned Erdos735Problem.lean](https://github.com/rjwalters/lean-genius/blob/b48d6729f20c9a4424bcd555a88ea0cea8ac7def/proofs/Proofs/Erdos735Problem.lean).
- [PR 43668](https://github.com/rjwalters/lean-genius/pull/43668) describes a repair
  to the higher-dimensional class predicate and a proved two-triples obstruction.
- [PR 43397](https://github.com/rjwalters/lean-genius/pull/43397) reports a general
  position theorem for higher-dimensional flats.

Those works include substantive proved results. This package does not import
that repository or reuse its code, and does not claim to supersede all of it.
It uses the ABKPR degree formula to prove a different, uniform incidence checker.
The full external project was not rebuilt or independently audited here.

## Official repository search and scope

On 2026-09-17, the official issue/PR inventory and a fresh exact-ID search did not
reveal a submission for `JSP-000603`. A textual hit for `jsp603` in issue 16 was a
local directory name in an unrelated Erdős 603 reproduction recipe, not this
problem. Absence from those searches does not establish world-first priority.

The official base reviewed was
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`.
The contribution is submitted as scoped formal evidence, without candidate,
recipient, catalog-status or award edits. Passing local checks does not establish
organizer acceptance or eligibility.
