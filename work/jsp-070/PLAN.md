# JSP-000070 24 小时形式化认领冲刺计划

## 靶与目标
- **主靶**：JSP-000070 — "For any integer set with distinct two-element sums, can another such set be found with no common nonzero differences?"（Sidon 型 / 不同两元素和）
- **状态**：Solved | Lean proof: Yes | Eligible: Yes | **Unclaimed** —— 数学与 Lean 均已存在，本冲刺的目标是：**验证 → 独立复核 → 打包提交认领**（吃"第一次发放先例"红利）
- **备胎**（同族，脚手架 100% 复用）：JSP-000043（不同子集和的最大元素下界）、JSP-000071（两个不同两元和集的总规模上界）
- **窗口**：2026-09-17 02:35 → 2026-09-18 02:35（北京时间），每 10 分钟一 tick，共 144 tick

## 阶段与 tick 任务表
| 阶段 | tick 范围 | 窗口 | 任务 | 完成判据 |
|---|---|---|---|---|
| D0-A | 0–11 | 0–2h | 读 catalog 详细条目（problems/catalog-0101-0200.md 内 070/043/071 三段）；确认证明源与 Lean repo 链接；克隆/下载到 work/jsp-070/repo/；验证 pinned commit 可构建 | 主靶 repo `lake build` 绿（或已切换备胎并在 PLAN.md/driver.json 记录原因） |
| D0-B | 12–35 | 2–6h | submission/ 四件套（award / citation / recipients / verification）+ manage.py 一键校验 + git init + 首提交 | manage.py 全绿 |
| D1-A | 36–119 | 6–20h | 每 tick 编译驱动：`lake build` 修错 → `#print axioms` 审计 → 独立验证说明（repo commit 哈希、Lean 版本、构建日志、定理清单） | 全量构建绿 + 零非商公理 + 验证说明草稿 |
| D1-B | 120–143 | 20–24h | 外部仓库 pinned commit + PR（正文占位符 RECIPIENT-JSP-000070-A）；按 docs/records.md 与 docs/templates/ 更新 awards/ 与 candidates/ 记录；写 state/final-report.md | PR 已开 + 记录已更新 + 最终报告完成 |

## 每 tick 协议
1. 读 state/driver.json（phase / tick / last_action / log）
2. 截止检查：当前时间 ≥ 2026-09-18T02:35:00+08:00 → 进入收尾（final-report.md + 停用定时任务）
3. 执行当前阶段的一个最小工作单元（上表粒度）
4. 更新 driver.json（tick+1、phase 推进、last_action、log 追加一行）
5. git commit（提交信息以 `JSP-070-tickNN` 开头）
6. 回复三行摘要（tick 号+阶段 / 本次动作 / 构建与下一步）

## 硬性规则
- 时间盒 9 分钟，超时立即收尾提交
- 一次只做一个工作单元，不并行推进多个阶段
- 禁止改动 work/jsp-637（另一对话的靶）
- 全部使用绝对路径；消息与脚本内路径用 `/` 分隔
- 禁止新增 axiom / sorry；`#print axioms` 仅允许标准库内置公理
- 主靶 repo 不可用/不可构建 → 切换备胎 000043 或 000071（同族），并记录原因
- 连续 6 tick 无实质进展 → 写 state/blockers.md 并停止，等待人工介入

## 提交物（D1-B 产出）
- 外部仓库 pinned commit + PR（RECIPIENT-JSP-000070-A 占位）
- work/jsp-070/submission/：award.yaml、citation.md、recipients.md、verification/（statement_comparison 记录、#print axioms 输出、构建日志）
- awards/ 与 candidates/ 记录（按 docs/records.md、docs/templates/ 的既有格式）
- state/final-report.md：各阶段完成情况、定理清单、commit 哈希、未完成项

## 参考
- 目录：I:/research/justin-sun-prize/problems/（索引在 README.md，明细在 catalog-0101-0200.md）
- 规则：I:/research/justin-sun-prize/docs/（records.md、grading.md、templates/）
- 脚本：I:/research/justin-sun-prize/scripts/manage.py
