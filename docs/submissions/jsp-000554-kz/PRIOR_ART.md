# Prior work and the requested incremental scope

Screened on 17 September 2026. The catalog's `Lean proof: No` does not
establish that no Lean proof exists.

## Existing formalization

The public [plby/lean-proofs source at
8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos682.lean)
already contains `Erdos682.erdos_682`, whose stated conclusion is the
density-one assertion of the original problem. Its header credits Ayla
Gafni and Terence Tao for the mathematics, and Codex and GPT-5.6 Sol for
the formalization. It also contains a conditional gap-18 construction.
This review inspected that source; it did not rebuild or independently
certify its dependency closure.

Consequently this package does not claim first formalization of Erdős 682
or a new proof of its main result. The existing density theorem is outside
the work claimed here. Its authors retain their credit. None of that
repository's proof code is imported or submitted in this package.

## Scope comparison

| Topic | Existing source inspected | This package |
| --- | --- | --- |
| Density one of good prime gaps | Stated and proved as `erdos_682` | Not claimed |
| A conditional exceptional gap-18 family | `erdos_conditional_counterexample` | Not claimed |
| General exact residue criterion for every gap length h >= 2 | No matching all-length residue-classification theorem found in the inspected file | `badGap_iff_residue_all` |
| Exact counting by these residue classes for any finite set of starting points | No matching theorem found in the inspected file | `count_badGaps_all` |
| Complete residue tables at h = 2, 4, 6, 8, 10, 12 | No matching tables found in the inspected file | Six checked classification corollaries |

The proposed value is a compact, separately reproducible formalization of
the finite reduction in Section 4 of Gafni--Tao, together with exact
small-gap classifications. This is known mathematics and supporting
formalization, not an improved asymptotic bound or a new mathematical
solution. Related roughness and coprimality lemmas overlap in mathematical
content with standard sieve infrastructure and the existing development.

The official repository issue/PR searches for `JSP-000554`, `682`,
`Erdos 682`, `Erdős 682`, and `rough numbers` returned no matching record
in the observed searches. These are bounded discovery checks, not a
guarantee of priority or absence of unindexed work. In particular, the
public source above exists despite the absence of a matching search result.

Please assess whether this incremental scope is useful and eligible as a
formalization contribution. A verified alternative implementation alone
does not establish entitlement to an additional award.
