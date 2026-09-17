# JSP-000078 / Erdos 58: arbitrary graphs

This package formalizes the chromatic upper bound and equality characterization
for arbitrary vertex types, using the existing finite-graph formalization.
The exported theorem is `JSP000078.erdos_58_exact_statement`.
The source and verification evidence are offered for contribution and eligibility
review, not as an announced award or a first-completion claim.

## Statement and mathematical correspondence

For any simple graph `G`, if the set of odd simple-cycle lengths is finite and
has cardinality at most `k`, then its chromatic number is at most `2*k+2`.
Equality holds if and only if it contains a copy of the complete graph on
`2*k+2` vertices. There is no finite, countable, connected, locally finite, or
nonempty vertex assumption; `k=0` and the empty graph are included.

Every finite induced subgraph inherits the odd-cycle-length bound. Apply the
existing finite theorem and graph-coloring compactness to obtain the global
bound. If the critical complete graph is absent, it is absent from each finite
induced subgraph. The finite theorem's equality characterization then lowers
each finite subgraph's bound to `2*k+1`. A second application of compactness
gives that lower bound globally. Conversely, a complete subgraph on `2*k+2`
vertices forces that many colors.

`oddCycleLengths_alignment` proves equality between the finite project's
predicate and the unchanged Formal Conjectures predicate. The final theorem
restates the exact quantifiers and conclusions from the pinned target source.
The finite core is imported as a proved theorem, not introduced as an axiom or
left as an assumption of the final theorem.

## Reproduction

Requirements: Git, Python 3, elan/Lake, network access, and enough disk space for
Lean and Mathlib. From this directory run:

```sh
bash scripts/verify.sh
```

The toolchain is Lean 4.33.0. Mathlib is pinned to
`db584cd6d46c92f209a44c0f1c829460d327499d`; `lake-manifest.json` fixes the
remaining dependencies. The script checks a fixed source-hash lock and downloads 35 byte-preserved upstream proof
modules, checks source constructs and definition identity, builds the finite
and general proofs, checks actual axiom output, and replays all 39 project
mathematical modules against a Mathlib-only environment.

On macOS installations where Python does not find the system CA store, use
`SSL_CERT_FILE=/etc/ssl/cert.pem bash scripts/verify.sh` if that CA file exists.
Do not disable TLS verification. A network failure is not a Lean proof failure.
The verified release ZIP also includes the 35 unchanged finite-proof modules.

The final success marker is written only after every stage succeeds. Actual
results and limitations are described in [VERIFICATION.md](VERIFICATION.md).
Mathlib dependency caches and the same Lean kernel are used; this is not a new
independent checker or a fresh replay of Mathlib itself.

## Contribution and existing submission

[PR #130](https://github.com/TheJustinSunPrize/awards/pull/130) already presents
the same arbitrary-graph extension, with public verification evidence. This
package explicitly acknowledges that overlap and makes no claim to first
formalization, mathematical discovery, or priority over that submission.
The additional finite-obstruction and predecessor-colorability lemmas in this
package do not change that overlap. Its kernel-replay utility is reused
unchanged from that submission, with attribution.

The submitting account requests review of the supplied candidate's
formalization, any necessary compilation repairs, and this reproducibility
package. Whether that contribution merits separate or joint recognition is a
maintainer/committee decision. Recipient identity confirmation remains pending;
the review placeholder is `RECIPIENT-JSP-000078-RANDYXIAN08-A`. This submission
is made with OpenAI Codex assistance and is not an independent referee report.

See [NOTICE](NOTICE) and [REFERENCES.md](REFERENCES.md) for the original finite
mathematics, finite Lean development, compactness, definitions, and replay
utility. Original third-party notices are retained. Apache-2.0 applies to the
proof and tooling. Catalog, eligibility, recipient, and award decisions are
not changed by adding this proof package.
