# JSP-000746 / Erdős #895 — independent Schur triples

A complete Lean 4 formalization of the following known result:

> Every triangle-free graph on the positive integers has three distinct,
> pairwise nonadjacent vertices `a`, `b`, and `a + b` in `[1,18]`.

The main theorem uses Mathlib's `SimpleGraph`, `CliqueFree 3`, and
`IsIndepSet`. It includes `0 < a` and `a < b`; addition is ordinary natural
addition, with no modular wraparound. The bound also answers the question for
all integer intervals `[1,n]` with `n ≥ 18`.

## Proof and trust boundary

We independently generated the finite SAT instance: one variable per possible
edge on `[1,18]`, negative clauses excluding triangles, and positive clauses
excluding independent Schur triples. Assuming both properties yields a
contradiction. A CaDiCaL LRAT trace supplies hints for explicit propositional
proofs, which Lean checks. The graph-theoretic wrapper discharges each input
clause from the actual graph assumptions.

SAT solving and Python generation are proof-discovery tools. The delivered
Lean source typechecks independently of those tools. All four main-theorem
axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

See [statement correspondence](STATEMENT.md),
[source and prior-work audit](evidence/SOURCES.md), and
[verification record](evidence/VERIFICATION.md).

## Reproduce

The project pins Lean `v4.34.0` and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` in the toolchain and manifest.
With `elan`, Python 3, and network access for first-time dependencies:

```sh
lake exe cache get
python3 scripts/verify.py
```

The normal Lean build does not invoke SAT solving or the generator. Compiled
Mathlib dependencies can be obtained from its cache. Optional proof-source
regeneration is documented in [PROOF_GENERATION.md](evidence/PROOF_GENERATION.md).

## Attribution and scope

This formalizes an existing mathematical result; it is not a claim to have
first solved the mathematical problem. The problem website credits Ben Barber
with the explicit bound 18 via SAT and personal communication. Earlier
qualitative results are attributed in [SOURCES.md](evidence/SOURCES.md).
Prior Lean work supplied a lower-bound witness on `[1,17]`; its inspected
positive theorem remained unfinished. No source from that project is copied.

Formalization applicant/contributor: **xpzwzwz**, assisted by **OpenAI Codex**.
Only the formalization contribution is claimed. This repository does not
assert that a prize has been awarded or eligibility has been approved.
First-party source is licensed under [MIT](LICENSE); dependencies retain their
own licenses.

## Official submission provenance

Applicant: `xpzwzwz`. Submitted for review of the Lean formalization contribution
for JSP-000746, with OpenAI Codex assistance disclosed above.

Immutable standalone proof source:
[commit 927bc61467102b7bcc34e07419dc585e3c370ee3](https://github.com/xpzwzwz/jsp-000746-lean/tree/927bc61467102b7bcc34e07419dc585e3c370ee3).
The Lean source, dependency pins, and proof certificates are copied unchanged.
This submission requests independent verification and prize consideration;
it makes no award decision and does not change eligibility or candidate records.
