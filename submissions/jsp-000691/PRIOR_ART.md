# Attribution and bounded prior-art review

## English

The mathematical necessary condition belongs to **Jie Ma and Quanyu Tang**.
This submission claims formalization work, not a new mathematical solution.

The definition `Erdos835.Property` is reproduced from Formal Conjectures, commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`, copyright 2025 The Formal Conjectures
Authors, licensed under Apache-2.0. The proof uses mathlib at
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, whose contributors and Apache-2.0
licence are retained upstream. The new implementation also uses Apache-2.0.

The proof was developed with ChatGPT assistance. The intended award role is Lean
formal verifier; no share for the pre-existing mathematical discovery is claimed.
Proposed recipient: `RECIPIENT-jsp-000691-A`, pending authorized confirmation.

The following public-source screening was performed on 2026-09-16:

| Source | Observed scope |
| --- | --- |
| [Formal Conjectures 835](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/835.lean) | States the general composite obstruction with an unproved body. |
| [Ma–Tang repository](https://github.com/QuanyuTang/erdos-problem-835/tree/7f131832bab5abfc903014ddb61efff21d56ae01) | Mathematical paper; no Lean source found in the inspected tree. |
| [lean-genius extension](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos835Incomplete01.lean) | Genuine proofs of surjectivity, window injectivity, and proper colouring. These are prior structural results; their mathematical content is not claimed as newly discovered here. No proof of the general composite obstruction was found there. |
| [plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e) | No dedicated Erdős 835 module found in the inspected tree. This is not semantic verification of every differently named file. |
| Official awards Issues/PRs | No submission covering JSP-000691 / Erdős 835 was found in the inspected public snapshot. |
| [Original problem discussion](https://www.erdosproblems.com/forum/thread/835) | The December 2025 report describes AlphaProof's `k=9` result and a Lean generalization to odd `k`; the author says the further generalization to every composite successor was not pursued in that work. This is significant prior partial formalization. |

Earlier AlphaProof work and other partial formalizations exist for this problem.
This screening therefore does **not** assert that Erdős 835 has never been
formalized in any scope. Nor does absence from these sources establish global
first-formalization priority. The precise new submitted scope is the uniform
prime-successor necessary condition, including even `k` with composite `k+1`.
Final priority and eligibility are for
the designated reviewers to determine.
