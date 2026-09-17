# JSP-000070 形式化验证冲刺 — 阶段报告

- 靶：**JSP-000070**（Erdős 问题 #42：整数集不同两元素和，Sidon 型；https://www.erdosproblems.com/42）
- 备胎：JSP-000043 / JSP-000071（未启用，主靶全程可用）
- 窗口：2026-09-17 02:35 — 2026-09-18 02:35（北京时间）
- 报告生成：2026-09-17（tick18，提交物已齐备，收件人确认为人工步骤）
- 总体状态：**submission-ready** · 记录状态 `pending-recipient-confirmation`

## 1. 各阶段完成情况

| 阶段 | 内容 | 状态 |
|---|---|---|
| D0-A | 锁定靶：证明源 plby/lean-proofs @ `1268917d`，Erdos42.lean（compact-Cayley 路线）；数学证明 Harjas Sandhu，形式化 Pawan Sasanka Ammanamanchi；验证 pinned commit 可编译（先 v4.33 后 v4.34） | ✅ 完成 |
| D0-B | 四件套（award.yaml / citation.md / recipients.md / verification/ 含 statement_comparison + `#print axioms` 记录）；`manage.py validate` = OK；全部入库 | ✅ 完成 |
| D1-A | 编译驱动：v4.34.0 current-release 重新验证绿（15 处 v4.34 API 适配，无数学改动）；`#print axioms` 审计 5 入口仅标准公理；独立验证说明（pinned 哈希、Lean 版本、构建日志、定理清单、复现步骤） | ✅ 完成 |
| D1-B | 记录确认态（sandbox 实证、statement v2、状态置回）；提交材料 `submission/PR.md`（PR 正文 RECIPIENT-JSP-000070-A 占位）；**遗留：收件人书面确认、awards/ 公告（人工步骤）** | 🟡 自动化部分完成 |

## 2. 验证证据链（commit 哈希）

| Commit | tick | 内容 |
|---|---|---|
| `4d1d3bd` | 02 | verify 工程就绪（mathlib v4.33.0 pinned `db584cd6`） |
| `4ae90b6` | 10 | mathlib 全库编译完成 8707/8707（v4.33 链） |
| `fbe0388` | 12 | D0-A 完成：编译绿 + axioms 零非商，进入 D0-B |
| `aa57cec` | 14 | **v4.34.0 current-release 重新验证绿**（15 处 `prod_le_one/prod_le_prod` → `prod_le_one₀/prod_le_prod₀`）；record.yaml → current_release: true |
| `0a48161` | 15 | D1-A 完成：独立验证说明（pinned/版本/哈希/复现/公理表） |
| `49d4007` | 16 | 四件套整批入库；`manage.py validate` = OK；statement v2 active |
| `74ce07c` | 17 | 确认态记录：sandbox 实证、status=pending-recipient-confirmation、PR.md 提交包 |
| `2b0f3a2` | 18 | 阶段报告 final-report.md 落盘（本文件） |
| `96276d8` | 19 | 复现三件套 + people 档案入库；.gitignore 卫生；blockers.md 落盘 |

上游 pinned：`github.com/plby/lean-proofs` @ `1268917deaaaa0d674f651287027baa26cea9920`
current-release 环境：Lean `leanprover/lean4:v4.34.0`，mathlib @ `5ed2965256430c3649e86755f9576b54eca72435`（v4.34.0，源码构建 8712 olean）

## 3. 定理清单与公理审计

| 定理 | 公理 |
|---|---|
| `Erdos42.CompactCayley.compact_cayley_clique` | `[propext, Classical.choice, Quot.sound]` |
| `Erdos42.CompactCayley.theorem_1_1_from_compact_cayley` | 同上 |
| `Erdos42.theorem_1_1_via_cayley` | 同上 |
| `Erdos42.erdos_42_via_cayley` | 同上 |
| `Erdos42.FormalConjecturesShape.erdos_42_via_cayley` | 同上 |

无 `sorryAx`、无新增公理、无 unsafe。适配版源码 SHA-256 `749BC7F7…A5446`；
olean（v4.34.0）SHA-256 `94ED070F…BBF06`。

## 4. 关键产物

- 验证证据：`candidates/verified-pending/jsp-000070/verification/`
  （record.yaml、statement.yaml·v2、current-release-v4.34.log、independent-verification.md、statements/STMT-jsp-000070-v1.yaml）
- 提交包：`work/jsp-070/submission/PR.md`
- 构建工程：`work/jsp-070/verify-current/`（lakefile pinned mathlib @ v4.34.0）

## 5. 未完成项（人工步骤，不阻塞自动管线）

1. **收件人书面身份确认**（RECIPIENT-JSP-000070-A → 实际署名）；
2. 确认后按 records.md 将记录移入 `awards/` 并公开 `announcement` 链接；
3. 若上游接受 PR：推送 v4.34 适配版补丁至 plby/lean-proofs 并关联验证证据。

## 6. 备注

- 主靶全程可用，备胎 000043/000071 未启用；
- 沙箱声明均有实证（非提升令牌 Medium Integrity、离线编译、无预编译产物）；
- 截止时刻复核：流程全部自动化项已完成，剩余人工步骤不依赖本冲刺。