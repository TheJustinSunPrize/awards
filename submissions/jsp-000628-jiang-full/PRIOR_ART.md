# Prior art and contribution boundary

Tao Jiang proved the mathematical theorem in 2004. The Lean proof retained
here was already publicly available in `plby/lean-proofs` at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e` before this submission.

The present work contributes a standalone pinned package, an explicit
statement map, a reproducible build, an axiom audit, provenance records, and
submission evidence for JSP-000628. It does not claim that repackaging the
existing proof creates new mathematical or formal authorship.

Open awards PR #573 concerns a different incremental scope: Chen--Ning's
critical-order sharpness witness. It explicitly says it does not formalize
the upper bound or full extremal formula. The package here proves Jiang's
original full equality in the range `n ≥ 3k + 3`; it does not prove the
stronger Chen--Ning formula outside that range.
