# Candidate citation: JSP-000070 (Erdős problem 42)

## English

For any integer set with distinct two-element sums (a Sidon-type set), can
another such set be found with no common nonzero differences?  This is Erdős
problem 42 (posed 1995, https://www.erdosproblems.com/42).

Status of this candidate record:

- Mathematical status: solved (proof contributor: Harjas Sandhu).
- Lean formalization: available (formalization contributor: Pawan Sasanka
  Ammanamanchi) in the public repository `github.com/plby/lean-proofs` at
  pinned commit `1268917deaaaa0d674f651287027baa26cea9920`, file
  `src/latest/ErdosProblems/Erdos42.lean`.
- Eligible to claim: yes, subject to independent verification and review.

Independent verification performed on 2026-09-17 (current release):

1. The pinned upstream source `Erdos42.lean` was rebuilt from source in an
   isolated Lake project against mathlib pinned at
   `5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`), Lean toolchain
   `leanprover/lean4:v4.34.0` (the currently released version).
2. Fifteen call sites of `Finset.prod_le_one` / `Finset.prod_le_prod` were
   adapted to the v4.34 API `prod_le_one₀` / `prod_le_prod₀`; the added
   explicit non-negativity hypotheses are all immediate (norm/abs
   non-negativity, or hypotheses already present in context). No mathematical
   content changed.
3. The build succeeded; the theorem
   `Erdos42.CompactCayley.compact_cayley_clique` compiled to a valid `.olean`.
4. An axiom audit (`#print axioms`) reports exactly
   `[propext, Classical.choice, Quot.sound]` — the three standard Lean kernel
   axioms only. No additional axioms and no `sorry` are used. The same audit
   is clean for the four further entry points
   `theorem_1_1_from_compact_cayley`, `theorem_1_1_via_cayley`,
   `erdos_42_via_cayley`, and
   `Erdos42.FormalConjecturesShape.erdos_42_via_cayley`.

See `verification/record.yaml`, `verification/statement.yaml`,
`verification/current-release-v4.34.log`, and
`verification/independent-verification.md` for details.

This is a candidate record published in `candidates/verified-pending/`. It is
not an award. Recipient identity confirmation and public announcement are
still pending.

## 中文

对任意整数组集合，若其两两元素和互异（Sidon 型），是否存在另一个同型集合
与之没有公共非零差分？此为 Erdős 问题 #42（1995 年提出）。

本候选记录状态：数学上已解决（证明贡献者 Harjas Sandhu）；Lean 形式化已发布
（形式化贡献者 Pawan Sasanka Ammanamanchi，仓库 `plby/lean-proofs`，
pinned commit `1268917d`，文件 `src/latest/ErdosProblems/Erdos42.lean`）。

2026-09-17 已完成 **current-release 独立验证**：以 Lean 4.34.0 +
mathlib v4.34.0（`5ed29652`）从源码重建（15 处 `prod_le_one/prod_le_prod`
调用点为适配 v4.34 API 改为 `prod_le_one₀/prod_le_prod₀`，仅补显式非负
前提，无数学改动）；构建成功；`#print axioms` 仅
`[propext, Classical.choice, Quot.sound]` 三个标准公理，无 `sorry`。

本记录为候选记录（`candidates/verified-pending/`），尚非奖项；收件人身份
确认与公开宣布待定。