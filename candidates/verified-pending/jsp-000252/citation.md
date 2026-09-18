# Candidate citation: 000252

## English

Subsets of a finite integer range with reciprocal sum one (catalog 000252).
S. Steinerberger (2024), *On a problem involving unit fractions*
(arXiv:2403.17041), main theorem: for all sufficiently large n, the number of
subsets S ⊆ {1,…,n} with Σ_{s∈S} 1/s ≤ 1 is < 2^(0.93·n).

Status of this candidate record:

- Mathematical status: solved (Steinerberger 2024, arXiv:2403.17041).
- Lean formalization: available in the public repository
  `github.com/shunfeng8421/jsp252-lean` at commit
  `e770ce3d9b7ac53c7ab088d87e22677406e7d26d`
  (Lean 4.35.0-rc1 + mathlib @ `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68`).
  The formal theorem `JSP252.main_bound` states
  ∃ N₀, ∀ n ≥ N₀, #{S ⊆ [n] : Σ_{s∈S} 1/s ≤ 1} ≤ 2^(0.93·n)
  (N₀ = 200000), the non-strict upper bound implied by the paper's bound.
- Verification: rebuilt on Windows 11 x86_64 from the pinned source with
  exit code 0; axiom audit clean — all entry theorems depend only on
  [propext, Classical.choice, Quot.sound]. See verification/record.yaml.

This is a candidate record for verification only — not an award decision.
Recipient identity is pending confirmation (placeholder RECIPIENT-JSP-000252-A).

## 中文

有限整数区间上倒数和为 1 的子集（catalog 000252）。
S. Steinerberger (2024)，《On a problem involving unit fractions》
(arXiv:2403.17041) 主定理：对一切充分大的 n，满足 Σ_{s∈S} 1/s ≤ 1 的
子集 S ⊆ {1,…,n} 的个数小于 2^(0.93·n)。

本候选记录状态：

- 数学状态：已解决（Steinerberger 2024, arXiv:2403.17041）。
- Lean 形式化：公开仓库 `github.com/shunfeng8421/jsp252-lean`
  提交 `e770ce3d9b7ac53c7ab088d87e22677406e7d26d`
  （Lean 4.35.0-rc1 + mathlib @ `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68`）。
  形式化定理 `JSP252.main_bound`：∃ N₀, ∀ n ≥ N₀, #{S ⊆ [n] : Σ 1/s ≤ 1} ≤ 2^(0.93·n)
  （N₀ = 200000），即论文严格界的非严格上界形式。
- 验证：在 Windows 11 x86_64 上由 pinned 源重建，退出码 0；
  公理审计干净——全部入口定理仅依赖 [propext, Classical.choice, Quot.sound]。
  详见 verification/record.yaml。

本记录仅为验证候选，不构成奖项决定。收件人身份待确认
（占位符 RECIPIENT-JSP-000252-A）。
