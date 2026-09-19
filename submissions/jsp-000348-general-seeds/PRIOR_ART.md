# Prior work, attribution and submission limits

## Mathematical sources

- [Tang, arXiv:2603.09939v1](https://arxiv.org/html/2603.09939v1), Theorem 1.4:
  arbitrary positive seeds of size at least two have eventually nondecreasing,
  unbounded excess. [Version 2, Section 6.1](https://arxiv.org/html/2603.09939v2#S6.SS1)
  retains the extension as a concluding remark. The mathematical conclusion
  belongs to that work, not to this submitter.
- [Erdős problem 423](https://www.erdosproblems.com/423): the original classical
  sequence and the unresolved asymptotic question.

## Existing Lean submission

[Awards PR #415](https://github.com/TheJustinSunPrize/awards/pull/415), linked
to [issue #416](https://github.com/TheJustinSunPrize/awards/issues/416), supplies
[Erdos423.lean at commit 6af50e76fc7d7bf6da0c43975998805fca5cb4a3](https://github.com/baobingzhang/jsp-000348-erdos423-lean/blob/6af50e76fc7d7bf6da0c43975998805fca5cb4a3/Erdos423.lean).
Its `IsHofstadterSeq` fixes `a 1=1` and `a 2=2`. It proves the classical
qualitative conclusions, a quantitative log-log lower bound, and existence
and uniqueness for that fixed seed. Its elementary comparison of two powers
of two already avoids importing Schinzel–Tijdeman or Beukers as axioms.

The current submission extends the quantification to every finite positive
seed, including unsorted and repeated entries, and gives a general
non-greedy theorem under eventual increase and block generation. Its main
arithmetic contradiction instead chooses a single odd-exponent power and
uses the gap between adjacent products `v(v+1)`.

The parity and finite-approximation code patterns were informed by and adapted
from that public Apache-2.0 source. This is disclosed in the source header and
[NOTICE](NOTICE); the full license is included. This package does not claim
independent rediscovery of the prior classical formalization. No global
first-formalization claim is made for the arbitrary-seed statement either.

## Scope and award status

The official catalog at base commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae` lists JSP-000348 as `Progress`,
`Lean proof: No`, and **`Eligible to claim: No`**. This package is submitted
as public evidence for a scoped formalization and consideration of that
specific contribution. It does not request that an open problem be marked
solved or that an award be announced.

The full asymptotic problem, the classical quantitative bounds, and award
eligibility remain outside the proved result. Repository checks and local
kernel verification do not establish organizer acceptance or a prize.
Any reward or recognition is subject to the organizers' published process
and decision.

The public submitter is `green3sf`; this is a self-submission. Development,
proof search, documentation and local verification were performed with
OpenAI GPT/Codex assistance. No human specialist review or affiliation with
the organizers is claimed.
