# Candidate citation: JSP-000071 (Erdős problem 43)

## English

How large can two sets with distinct two-element sums be in total if their
nonzero difference sets are disjoint?  This is Erdős problem 43 (posed before
1982, https://www.erdosproblems.com/43).

Status of this candidate record:

- Mathematical status: solved (proof contributor: Kevin Barreto).
- Lean formalization: available (formalization contributor: Boris Alexeev) in
  the public repository `github.com/plby/lean-proofs` at pinned commit
  `1268917deaaaa0d674f651287027baa26cea9920`, file
  `src/latest/ErdosProblems/Erdos43.lean`.
- Eligible to claim: yes, subject to independent verification and review.

Independent verification performed on 2026-09-18 (current release):

1. The pinned upstream source `Erdos43.lean` was rebuilt from source in an
   isolated Lake project against mathlib pinned at
   `5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`), Lean toolchain
   `leanprover/lean4:v4.34.0` (the currently released version). It depends on
   `ErdosProblems.Erdos862` (same repository, same pinned commit), which was
   rebuilt in the same project after removing an unused leftover import
   (`PrimeNumberTheoremAnd.Consequences` — the file references no symbol from
   it, verified by full-file search).
2. The build succeeded; the theorems
   `Erdos43.not_erdos_43` and `Erdos43.not_erdos_43_part_ii` compiled to
   valid `.olean` artifacts.
3. An axiom audit (`#print axioms`) reports exactly
   `[propext, Classical.choice, Quot.sound]` — the three standard Lean kernel
   axioms only. No additional axioms and no `sorry` are used.
4. Attribution: the upstream Lean formalization `Erdos43.lean` is authored by
   Boris Alexeev (credited, not claimed); the solver is Kevin Barreto
   (credited, not claimed). This submission claims only the independent
   v4.34 verification work and the preparation of this record.

See `verification/record.yaml`, `verification/statement.yaml`,
`verification/current-release-v4.34.log`, and
`verification/independent-verification.md` for details.

This is a candidate record published in `candidates/verified-pending/`. It is
not an award. Recipient identity confirmation and public announcement are
still pending.

## 中文

两个互异的双元素和（Sidon 型）集合，若其非零差集不相交，两者合计最大能有多
大？此为 Erdős 问题 #43（1982 年前提出）。

本候选记录状态：数学上已解决（证明贡献者 Kevin Barreto）；Lean 形式化已发布
（形式化贡献者 Boris Alexeev，仓库 `plby/lean-proofs`，pinned commit
`1268917d`，文件 `src/latest/ErdosProblems/Erdos43.lean`，依赖同仓库
`ErdosProblems.Erdos862`）。

2026-09-18 已完成 **current-release 独立验证**：以 Lean 4.34.0 + mathlib
v4.34.0（`5ed29652`）从源码重建（Erdos862 移除了一个未使用的遗留 import
`PrimeNumberTheoremAnd.Consequences`，全文检索确认无引用，无数学改动）；
构建成功；`#print axioms` 仅 `[propext, Classical.choice, Quot.sound]` 三个
标准公理，无 `sorry`。归属说明：上游形式化作者 Boris Alexeev（credit，非
claim）；证明者 Kevin Barreto（credit，非 claim）；本提交仅 claim 独立 v4.34
验证与记录整理。

本记录为候选记录（`candidates/verified-pending/`），尚非奖项；收件人身份
确认与公开宣布待定。
