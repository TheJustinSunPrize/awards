# JSP-000070 交接文档 — 交 hermes 执行提交

> 生成：2026-09-17 23:45（+08:00）· 由主会话整理，供 hermes 直接接手提交流程。
> 总状态：**submission-ready** · 记录状态 `pending-recipient-confirmation` · bundle-ready（22 条目）。

## 1. 靶与数学内容

- **JSP-000070** = Erdős 问题 #42（https://www.erdosproblems.com/42）：
  整数集不同两元素和（Sidon 型）。
- 定理（正式陈述，`STMT-jsp-000070-v2`）：
  `Erdos42.CompactCayley.compact_cayley_clique (ell : Nat) (eta : Real) (h_ell : 2 <= ell) (h_eta : 0 < eta) :
   exists eps, 0 < eps ∧ exists p0, forall (p : Nat) [inst : Fact (Nat.Prime p)], p0 < p ->
   forall (T : Finset (ZMod p)), Erdos42.SymmetricFinset T -> 0 ∉ T -> eta * p <= T.card ->
   Erdos42.FourierUpperIndicator T eps -> exists C, C.card = ell ∧ Erdos42.CliqueInCayley T C`
- 原始证明源（上游）：`github.com/plby/lean-proofs` @ `1268917deaaaa0d674f651287027baa26cea9920`
- 数学证明：Harjas Sandhu；形式化：Pawan Sasanka Ammanamanchi（people/ 档案已入库）。

## 2. 验证证据（可复现）

| 项 | 值 |
|---|---|
| Lean 工具链 | `leanprover/lean4:v4.34.0`（current-release） |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435`（v4.34.0，源码构建 8712 olean，无 lakecache） |
| 源码 SHA-256 | `749BC7F780F5673A6D18A0C76778951C8A5858046D462CEF36C98D87980A5446`（v4.34 适配版） |
| olean SHA-256 | `94ED070F…BBF06`（v4.34.0） |
| 构建/公理日志 | `candidates/verified-pending/jsp-000070/verification/current-release-v4.34.log` |
| 公理审计（5 入口） | 均仅 `[propext, Classical.choice, Quot.sound]`，无 sorryAx、无新增公理、无 unsafe |

5 个入口定理：
1. `Erdos42.CompactCayley.compact_cayley_clique`
2. `Erdos42.CompactCayley.theorem_1_1_from_compact_cayley`
3. `Erdos42.theorem_1_1_via_cayley`
4. `Erdos42.erdos_42_via_cayley`
5. `Erdos42.FormalConjecturesShape.erdos_42_via_cayley`

v4.34 适配说明：15 处 `Finset.prod_le_one/prod_le_prod` → `prod_le_one₀/prod_le_prod₀`
（v4.34 起需要 `[MulLeftMono N]`，ℝ 无法合成；`₀` 变体显式非负前提，可在 ℝ 上合成）。**纯机械适配，无数学改动。**

复现：
```
cd work/jsp-070/verify-current
lake build        # 或 lake env lean Erdos42.lean（末尾含 #print axioms 审计）
```

## 3. 交付物位置（全部在 I:/research/justin-sun-prize 仓库内）

```
candidates/verified-pending/jsp-000070/
├── award.yaml                          # status: pending-recipient-confirmation
├── citation.md                         # ## English + ## 中文 双段
├── recipients.md                       # RECIPIENT-JSP-000070-A 占位（第 5 节待办 1）
└── verification/
    ├── record.yaml                     # checkers 全部 current_release=true + pass；sandbox 三项=true
    ├── statement.yaml                  # STMT-jsp-000070-v2 active；mathlib 5ed29652
    ├── statements/STMT-jsp-000070-v1.yaml   # superseded（保留）
    ├── current-release-v4.34.log       # 2957 B；sha256 f484eb28…
    └── independent-verification.md     # 哈希/复现步骤/沙箱声明 第 7 节

work/jsp-070/
├── submission/
│   ├── PR.md                           # 上游 PR 草稿（正文占位 RECIPIENT-JSP-000070-A）
│   ├── README-SUBMISSION.md
│   ├── .gitignore                      # *.zip
│   └── jsp-000070-submission-bundle.zip # 130,058 B；22 条目（1 份 PR.md + 3 份 people + 4件套 + 复现工程 + state）
├── verify-current/                     # 复现工程（Lakefile 三件套 + Erdos42.lean + ScratchTC.lean）
└── state/
    ├── driver.json                     # tick 71；phase D1-B
    ├── final-report.md                 # 阶段报告（含完整 commit 链）
    ├── blockers.md                     # 3 项人工阻塞
    └── HANDOFF-TO-HERMES.md            # 本文件

people/curators/jsp070-verifier.yaml
people/curators/pawan-sasanka-ammanamanchi.yaml
people/verifiers/jsp070-verifier.yaml
```

仓库校验：`python scripts/manage.py validate` → **OK**（每 10 分钟待命 tick 复核通过）。

## 4. 关键 commit 链（main 分支）

| Commit | 内容 |
|---|---|
| `4d1d3bd` | verify 工程就绪（mathlib v4.33.0 pinned） |
| `fbe0388` | D0-A 完成：编译绿 + 公理零非商 |
| `aa57cec` | **v4.34.0 current-release 重新验证绿**（15 处 `₀` 适配） |
| `0a48161` | D1-A 完成：独立验证说明 |
| `49d4007` | 四件套入库；validate=OK；statement v2 active |
| `74ce07c` | 确认态：sandbox 实证、pending-recipient-confirmation、PR.md |
| `2b0f3a2` | final-report.md |
| `96276d8` | 复现三件套 + people 档案；.gitignore；blockers.md |
| `f0cc63c` | tick71 待命（最新） |

## 5. 剩余人工步骤（hermes 接手清单）

1. **收件人书面确认**：把 `recipients.md` 与 `PR.md` 中的 `RECIPIENT-JSP-000070-A`
   替换为真实署名（身份经确认流程核实后再替换，勿在未确认时公告）。
2. **awards/ 迁移与公告**：按 `docs/records.md` 把该候选记录从
   `candidates/verified-pending/jsp-000070/` 迁移到 `awards/`，状态置 active，
   附公开 announcement 链接；更新 citation/recipients 为正式版。
3. **上游 PR 推送授权**：将 v4.34 适配补丁推送至 `plby/lean-proofs`
   （pr 正文已备于 `submission/PR.md`），并关联本验证证据（pinned 哈希、日志、独立验证说明）。

## 6. 硬性规则（沿用）

- 数据源仓库根：`I:/research/justin-sun-prize`（绝对路径操作）；
- **禁止**改动 `work/jsp-637`（另一对话的靶）；禁止新增 axiom/sorry；
- 每 tick 必须 git commit（信息以 `JSP-070-tickNN` 开头）；
- 沙箱声明（network_disabled/prebuilt_artifacts_ignored/unprivileged_user=true）
  已有实证（非提升令牌 Medium Integrity S-1-16-8192、离线源码构建），勿改回 false。