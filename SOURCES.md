# Sources and contribution boundary

- Official problem: [JSP-000360](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000360).
- Original problem index: [Erdos #441](https://www.erdosproblems.com/441).
- Yong-Gao Chen and Li-Xia Dai, *Sequences with bounded l.c.m. of each pair of
  terms, III*, Acta Arithmetica 128 (2007), 125-133,
  [publisher PDF](https://www.impan.pl/shop/publication/transaction/download/product/82089).
  Theorem 1(ii) provides a stronger quantitative result. The present construction
  uses factorials to simplify the divisibility dependencies and only claims
  unbounded additive improvement.
- [Earlier Lean proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos441.lean),
  pinned commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, was inspected before
  selecting this scope. It gives an infinite family with one extra element.
  Its header attributes the mathematics to Chen and Dai and the formalization
  to Codex and GPT-5.6 Sol. This project was developed with OpenAI Codex assistance.
  The square-only standard-set and admissibility definitions follow that framing;
  the unbounded-offset construction is separately implemented here.

As of the selection check, the official catalog still said Solved / Lean No /
Eligible No. That does not establish that no external Lean proof exists. Searches
for 000360 and 441 found no official PR; this is limited search evidence, not a
priority or exclusivity guarantee. No award or identity record has been created.
