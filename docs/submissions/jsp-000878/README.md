# JSP-000878 — full-statement verification attempt

**Status: VERIFIED by the recorded local technical checks.** All 29 attributed proof modules and the two new statement/bridge modules compiled; the three final axiom audits contain only `propext`, `Classical.choice` and `Quot.sound`; same-toolchain `leanchecker` replayed exactly 31 problem/bridge modules and exited 0; the false-arithmetic negative control was rejected. [Machine-readable receipt](evidence/verification.json). This is not independent review or an eligibility/award decision. No first-formalization priority is claimed.

The original [Erdős problem 1058](https://www.erdosproblems.com/1058), accessed 2026-09-17, asks whether only finitely many positive integers n have every prime divisor of n!+1 among the first two primes strictly larger than n. Florian Luca proved that exactly n=1,2,3,4,5 satisfy this condition (*Mathematics of Computation* 70 (2001), 893–896, [DOI](https://doi.org/10.1090/S0025-5718-00-01178-9)). The separate 2004 edition of Guy's book and 2025 webpage edit are not discovery dates; see [existing issue76](https://github.com/TheJustinSunPrize/awards/issues/76).

An existing public [Lean formalization](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1058.lean) credits Codex and GPT-5.6 Sol and is pinned here to commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The complete local source closure has 29 modules. Its classification is the substantive imported theorem; we do not claim authorship of that proof. The new [statement bridge](proof/Main.lean) states the full predicate, the equivalent bound 1<=n<=5, finiteness, and an escaping-prime consequence for every n>=6. A restatement is not a new mathematical result or proof of priority.

The source uses zero-indexed primes p(0)=2. The preceding interval endpoint for index 0 is conventionally 1, so n=1 is included without claiming that 1 is prime. For n=1 through 5, n!+1 is respectively 2,3,7,25,121; their prime supports are allowed. These five examples alone do not exclude any larger n. That exclusion requires the full imported proof, including its analytic bound and finite arithmetic certificates; the final theorem is compiled from that complete closure rather than inferred from these examples.

Local toolchain: Lean 4.34.0, Mathlib tag v4.34.0 at `5ed2965256430c3649e86755f9576b54eca72435`. The upstream source header specifies 4.33.0, so this run additionally tests compatibility with 4.34.0. Mathlib's complete build passed after obtaining available official caches and compiling the two unavailable cached modules. The complete problem closure subsequently compiled, including two tactic-only compatibility fixes; see the [reproduction instructions](proof/README.md) and [evidence guide](evidence/README.md).

No candidate/award record, recipient identity, signature or official status is changed. Per the [official FAQ Q8](https://hejustinsun.com/zh/prize/faq), earlier public source chronology matters even if no awards PR matches the identifier. This packet cannot claim first formalization based on a later local rebuild. Any joint-window or Contribution consideration requires organizer determination. No prize-claim email has been sent.

## Reviewable evidence

- [Exact statement, proof map and attribution](statement-and-attribution.md).
- [Pinned source closure](proof/source-lock.json) and [tactic-only compatibility diff](proof/compatibility.patch).
- [Reproduction procedure](proof/README.md), [actual compile/axiom output](evidence/compile-JSP000878.Main.log), [replay log](evidence/leanchecker.log), and [evidence interpretation](evidence/README.md).
- [Project validation and 22 passing tests](evidence/project-checks.log).
- [Pending review/identity status](review-status.json); decision remains null.
- [Packet SHA-256 manifest](manifest.json), excluding the manifest itself.

The initial 29-module compilation is retained with checked receipts rather than falsely described as rerun in the final command. The two statement/bridge modules, final axiom audit, replay and negative control were executed by the final runner. Imported Mathlib was reused during replay. Historical failures and the earlier resource timeout are preserved separately from successful final evidence.
