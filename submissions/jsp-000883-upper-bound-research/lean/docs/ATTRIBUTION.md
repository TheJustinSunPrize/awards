# Attribution and dependency boundaries

The problem originates with Paul Erdős and John L. Selfridge. Monier's factorial
bound and Cambie's k*LCM bound remain their mathematical results. The four target
definitions retain the previous research package's meaning and match the specified
Formal Conjectures / Erdős 1063 better_upper formulation.

The earlier O(LCM) construction and valuation argument were developed in the
conversation that produced the v0.1 research note (awards PR #498). The present
addition is an integer-product/coprimality proof route and Lean proof-source bodies.
It is AI-assisted work. The locally repaired version now has successful build,
exact-type, axiom and native replay receipts; these are not independent human review.

The following source was inspected before writing the new cancellation route:

https://github.com/pcycho/erdos1063-cambie/blob/396c09bfdf4cf8306261b8176a1917aa72135459/Cambie.lean

That file formalizes Cambie's OLDER k*LCM bound and uses quotient products,
binomial recurrence, positive-factor cancellation, and coprimality. Several short
API idioms and elementary recurrence/coprimality steps here adapt that approach.
The old result and its formalization are not claimed as new. The inspected source
is Apache-2.0 licensed and credits Cambie for the mathematics; its repository
records pcycho/Codex-assisted formalization. No part of PR #601's seven-module
proof implementation is copied into this package.

For prime distribution, we reuse the public theorem `chebyshev_asymptotic` from:

https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/PrimeNumberTheoremAnd/Consequences.lean

This is backed by the Prime Number Theorem + development of Alex Kontorovich,
Terence Tao, and collaborators, with its credited library contributors and the
pinned plby port. The fetcher retains their original files byte-for-byte. It checks
Git blob identities, records source URLs and SHA-256 hashes, and does not change
proofs, add axioms, strip notices, or relicense those files. The nine-module PNT dependency closure is included and compiled in this version,
with a successful transitive axiom audit and native per-module replay.

Mathlib and its dependency authors retain their credits. Their sources and
compiled caches are external dependencies, not original contributions here.

The project LICENSE applies to newly supplied source/documentation only, subject
to upstream notices. There is no recipient nomination, identity certification,
prize decision, assignment of payment, or first-priority assertion.
