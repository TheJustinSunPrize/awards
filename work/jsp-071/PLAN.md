# JSP-000071 形式化验证 · 冲刺计划（复用 070 已验证环境）

## 0. 目标
用 Lean 4.34.0 current-release 形式化 **JSP-000071**（Erdős #43，Sidon 型双元素和），
并按 Justin Sun Prize 提交规范打包（四件套 + manage.py validate + 外部仓库 pinned commit）。
**优势：与 JSP-000070 同仓库、同 pinned commit、同族、直接 import 已验证的 Erdos42** ——
环境零成本复用，属"低边际成本扩展"。

## 1. 问题陈述（catalog-0001-0100.md:1267）
- 编号：JSP-000071
- 标题：How large can two sets with distinct two-element sums be in total if their nonzero
  difference sets are disjoint?
- 领域：Number theory / Sidon sets / Additive combinatorics
- 状态：Solved（Kevin Barreto）；Lean proof：Yes（Boris Alexeev）
- 上游 Lean 源：`github.com/plby/lean-proofs @ 1268917deaaaa0d674f651287027baa26cea9920`
  → `src/latest/ErdosProblems/Erdos43.lean`（已在本地 `work/jsp-070/repo/` 克隆中）
- Historical bounty: $100；Eligible to claim: Yes；44 年

## 2. 定理形态（Erdos43.lean 两个入口）
- `theorem not_erdos_43 : ¬ …`（主体命题）
- `theorem not_erdos_43_part_ii : ¬ …`（第二部分）
- 辅助：`IsSidon`、`maxSidonSubsetCard`、`f` + 24 个声明（private lemma 为主）
- 依赖：`import Mathlib` + `ErdosProblems.Erdos42`（已验证）+ `ErdosProblems.Erdos862`（同仓库）

## 3. 环境（已侦察确认，与 070 完全一致）
- Lean v4.34.0 current-release；mathlib `5ed29652…`（源码构建 8712 olean，MATHLIB_CACHE_DISABLE=1）
- 复现工程：`work/jsp-070/verify-current/`（lakefile.lean + lean-toolchain + lake-manifest.json 三件套已入库）
- 策略：**直接在 verify-current 工程内添加 `Erdos43.lean` 副本**（保留 import 相对路径
  `ErdosProblems.Erdos42` 可用），复用已验证的 Erdos42.lean
- 注意：071 的定理含取否（¬），审计时同样要求仅 [propext, Classical.choice, Quot.sound]

## 4. 任务清单（tick 粒度，10 分钟/ tick）
| tick | 内容 | 验收 |
|---|---|---|
| D0-A-1 | 计划书 + driver + 复制 Erdos43.lean 入 verify-current + 试编译 | 首个错误定位 |
| D1-A-2 | v4.34 机械适配（prod_le_*₀ 等，若有）+ lake build 修错 | 编译绿 |
| D1-A-3 | #print axioms 审计（not_erdos_43 / not_erdos_43_part_ii）+ 独立验证说明 | 零非标准公理 |
| D1-B-4 | 四件套复制模板改 ID（award/citation/recipients/verification 4 文件）+ 日志 | validate 预备 |
| D1-B-5 | manage.py validate + bundle 打包 + final-report + commit | validate=OK |
| 收尾 | HANDOFF 附录更新（071 段落） | 可交 hermes |

预算：**5-8 tick（50-80 分钟）**，比 070 快一个数量级。

## 5. 关键风险与回退
- Erdos43 若含 v4.34 新破坏点（如 Finset.prod 系列）→ 同 070 的 `₀` 变体适配，模式已成熟
- 若 import 链有 Erdos862 的额外依赖问题 → 检查 Erdos862.lean 是否也需适配（同仓库同 commit，
  大概率无需；若有，2-3 个 tick 内机械处理）
- 收件人归属：catalog 标注形式化者 Boris Alexeev；与 070 相同，占位符 RECIPIENT-JSP-000071-A
  等书面确认后替换
- 若 6 tick 无实质进展 → 写 blockers.md 停止等待人工

## 6. 硬性规则（沿用 070）
- 数据源仓库根：I:/research/justin-sun-prize（绝对路径）
- 禁止改动 work/jsp-637 与 work/jsp-070 的已验证交付物（只读引用）
- 禁止新增 axiom 与 sorry；每 tick git commit（JSP-071-tickNN 前缀）
- 时间盒 9 分钟，超时立即收尾提交
