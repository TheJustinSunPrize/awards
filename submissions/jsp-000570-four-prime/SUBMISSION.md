# Submission scope: JSP-000570 / Erdős 700

This packet requests review of a new four-prime sufficient condition as partial progress under section 4.2 of the [published selection rules](https://www.hejustinsun.com/prize/rules). The exact Lean theorem is `Erdos700.FourPrime.four_prime_exact`; its full type, the definition of `f`, and its transitive axiom list are in [the audit log](verification/canonical-audit.log).

The preceding three-prime / exponent-2/3 result and its Lucas–Maynard strategy are credited in [the mathematical note](docs/proof.md). The contribution proposed for Lean review is the **local four-prime criterion**. The separate infinite-family / exponent-3/4 argument uses Maynard and is human-readable mathematical context, not a formally verified theorem in this packet. No first solution of the already answered square-root infinitude question is claimed.

The local proof was rebuilt from source with the pinned toolchain and dependency manifest. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the root theorem's axiom list. Prebuilt Mathlib dependency caches were reused; this is not a network-isolated run or an independent alternative proof checker. The internal AI-assisted semantic audit is not external peer review or designated organizer verification.

No full-entry solved status, eligibility flag, award record, payment, or tier is proposed. Historical priority, statement correspondence, significance, verification, and attribution are submitted for review. The limited literature and current-PR checks are negative checks, not guarantees of worldwide novelty.

Recipient attribution remains `RECIPIENT-JSP-000570-A`, pending confirmation. No recipient identity, private contact, payment data, signed verification certificate, or committee decision is asserted. The preparation used OpenAI Codex; the submitter and internal reviewers have an interest in this work's acceptance.

The packet has its own Apache-2.0 [license](LICENSE), preserving the source attribution in `Minimum.lean`. It does not redistribute the predecessor's manuscript, Lean, or Mathlib.
