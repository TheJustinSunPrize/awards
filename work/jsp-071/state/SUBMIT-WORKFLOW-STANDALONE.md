# JSP 候选记录提交流程指南（独立可执行版）

> 给另一个 AI 使用：本文件完整描述如何把一份**已完成 Lean 验证的研究成果**提交到
> `github.com/TheJustinSunPrize/awards`。按步骤执行即可，不需要额外上下文。
> 它依赖：`gh`(GitHub CLI，已登录)、`git`、Python 3.10+、能访问 GitHub。

---

## 0. 前置：你手上应有哪些"研究数据"

开始前确认以下验证产物已齐备（缺少则先补，这是提交的硬前提）：

- [ ] **上游 pinned 证明源**：`<repo-owner>/<repo>` @ 固定 commit（如 `plby/lean-proofs@1268917d`），含形式化文件（如 `Erdos42.lean`）
- [ ] **current-release 复验绿**：用最新 Lean 工具链 + 对应 mathlib 从源码重建通过（离线、`MATHLIB_CACHE_DISABLE=1`）
- [ ] **公理审计**：`#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`，无 `sorry`（对全部入口定理）
- [ ] 构建日志、源码 SHA-256、定理清单、复现步骤
- [ ] 收件人真实署名或确认意愿（未确认则用占位符，见 §4）

---

## 1. 官方是双轨制（必须两条都走）

| 轨 | 通道 | 作用 |
|---|---|---|
| 候选记录 | **提 PR**，记录进 `candidates/verified-pending/<entry-id>/` | 提交验证产物本身，CI 校验结构 |
| 参与/归属 | **开 issue 表单**（`[Recipient]`） | 让维护者 review 收件人归属 |

仓库 `config.yml` 设 `blank_issues_enabled: false`，只用 4 个模板：
`recommend-problem` / `recommend-recipient` / `correction` / `dispute`。
已完成验证 + 已确认收件人 → **`recommend-recipient`** 表单。

> 只提 PR 不够。官方 README/CONTRIBUTING 的"参与"走 issue 表单，漏了会影响评审。

---

## 2. 准备环境

```sh
# 克隆官方仓库 + fork 到你自己的账号（假设账号为 YOURLOGIN）
gh repo clone TheJustinSunPrize/awards && cd awards
gh repo fork --remote=true        # 建立 fork remote，默认名 origin 指向官方，新 fork 为你的
git checkout -b candidate/jsp-XXXXXX
```

> 条目 ID 统一格式 `jsp-xxxxxx`（如 `jsp-000070`）。

---

## 3. 记录文件布局与内容

```text
candidates/verified-pending/<entry-id>/
    award.yaml            # 核心：问题、收件人、验证、冲突、状态
    citation.md           # 评审叙事，必须含非空 ## English 段
    recipients.md         # 收件人署名，同样必须含 ## English 段
    verification/
        record.yaml       # pinned 源+commit、toolchain、定理+axioms、sandbox、artifacts(sha256+bytes)
        statement.yaml    # 版本化正式陈述（active）
        statements/<old-id>.yaml   # 旧版留档（status: superseded）
        <build-log>.log   # 大日志留外部归档，仅存 archive 路径+sha256+bytes
```

权威字段形状：`data/schema/award.schema.json`、`verification-record.schema.json`、
`statement.schema.json`。**schema 拒绝未知字段 / YAML 别名 / 重复键 / symlink**。

### 3.1 award.yaml（模板）

```yaml
id: jsp-xxxxxx
batch: null
problem:
  source: "Erdos problems list"        # 按实际问题改
  number: 42
  title_en: "..."                       # 问题英文标题
  posed: { year: 1995, basis: stated, citation: "https://..." }
  resolved: null
recipients:
  - id: your-id                         # 收件人 ID（见 §4）
    affiliation: "Independent researcher"
    contribution_en: "Independent verification of the pinned Lean formalization ... and preparation of this submission."
    confirmation: "https://github.com/YOURLOGIN"   # 授权公开主页
verification:
  peer_review: null
  formal:
    record: verification/record.yaml
    statement: verification/statement.yaml
  independent_review: null
conflicts: []
status: pending-recipient-confirmation
revocation: null
decision: null                          # 候选记录 decision 必须为 null
```

### 3.2 record.yaml 关键字段

- `repository` / `commit`：pinned 上游源 + 固定 commit
- `toolchain`：`language_version`（如 "4.34.0"）、`library_commit`、`meets_minimum_safe_version: true`
- `theorems`：每个入口定理一行，`axioms: [propext, Classical.choice, Quot.sound]` + `clean: true`
- `environment`：架构、镜像、构建方式（source-built 注明）
- `sandbox`：`network_disabled: true`、`prebuilt_artifacts_ignored: true`、`unprivileged_user: true`
- `attribution`：`proof_route`（写明数学证明者、形式化者）、`third_party: true`、`note_en`（说明只做了机械适配、无数学改动）
- `artifacts.build_log`：只存 `archive` 路径 + `sha256` + `bytes`
- `performed_by` / `performed_at`

### 3.3 citation.md / recipients.md

- 必须含非空 `## English` 段；可附加 `## 中文` 段。
- citation：说明问题、数学状态（solved + 证明者）、形式化状态（pinned 源）、独立验证过程与结果、当前是候选非奖项。
- recipients：英文段列收件人 `id`、姓名、贡献、确认状态。

---

## 4. 收件人确认规则（易错，务必遵守）

- 未确认身份前用占位符 **`RECIPIENT-<ENTRY>-A`**，**绝不能**把未确认真名放进
  title / body / 附件 / commit（官方明文禁止）。
- 确认后：`recipients.md` + `award.yaml` 用真实 `id`，`confirmation` 指向**授权公开主页**
  （如提交账号的 GitHub profile）。私密证件 / 联系方式 / 协议 / 支付一律不进仓库。
- **归属治理铁律**：只 claim 自己确实做的贡献。数学证明者、形式化者走
  `attribution.proof_route` credit（官方 `attribution.md` 明确允许 "credited using
  published sources"），**绝不**把他们列为你的 recipients 收件人。
  - 反面教训：曾有人替不控制的作者注册收件人，因"引用非其控制的仓库、无作者书面确认"
    被要求撤回。**由做了验证 / 控制候选记录的账户提交才合规。**

---

## 5. 本地验证

```sh
python3 -m venv .venv && source .venv/bin/activate
python -m pip install -r requirements.txt
python scripts/manage.py validate   # schema + 跨文件约束（提交前必须 = OK）
python scripts/manage.py links      # 本地 md 链接/锚点
python scripts/manage.py build      # 生成 data/*.json（确定性，须一并入库）
python scripts/manage.py check      # 对比已提交 json 与再生成
python -m unittest discover -s tests -v
```

- **people/ 档案**：确认收件人后要加 `people/recipients/<id>.yaml`，验证者可加
  `people/verifiers/<id>.yaml`、`people/curators/<id>.yaml`。
- **data/*.json**：`manage.py build` 生成后**必须**提交（否则 CI data-consistency 失败）。
- **Windows blobless clone 坑**：本机 `unittest` 可能有少量用例失败（symlink 权限
  WinError 1314 + 缺 blobless git 历史做 history-immutability 检查）——**环境性**，
  与记录内容无关，Linux CI 不受影响。PR 里如实说明即可，别误判为记录问题。

---

## 6. 提交：PR + [Recipient] issue

### 6.1 提交并开候选记录 PR

```sh
git add candidates/verified-pending/<entry-id>/ people/ data/
git commit -m "candidate: verified-pending record for <entry-id> (<问题>)"

git push fork candidate/jsp-XXXXXX
gh pr create -R TheJustinSunPrize/awards \
  --base main \
  --head YOURLOGIN:candidate/jsp-XXXXXX \
  --title "candidate: verified-pending record for <entry-id> (<问题>) + confirmed recipient" \
  --body "提交说明：pinned 源、复验环境、axioms 审计、validate=OK、确认的收件人。"
```

**fork PR 的 CI 行为（正常，别慌）**：fork 首次贡献，三个工作流
（Validate / Build data / Data consistency）全为 `action_required`，PR 停在
`BLOCKED`——**等维护者批准**才跑。这不是你方问题。
在 PR 里发一条英文评论说明：本地 validate 绿 + fork 首次 CI 待维护者批准 + 本机
单测失败是环境性的。

### 6.2 开 [Recipient] issue（官方参与通道）

`gh issue create -R TheJustinSunPrize/awards`，标题 `[Recipient] <entry-id>: <贡献摘要>`。
正文按模板 5 个字段填（用 `gh issue create` 需以 `--title` + `--body-file` 传，
因为 `blank_issues_enabled: false`）：

1. **Related problem or entry**：条目 ID + 问题描述 + 官方链接 + 候选记录 PR 链接。
2. **Recipient placeholder or confirmed public ID**：真实 `id` + 姓名 + 公开主页。
3. **Contributions and evidence**：**区分**证明者 / 形式化者 / 独立验证者三方贡献；
   只 claim 你自己的验证贡献，其他人 credit。
4. **Confirmation status**：书面确认已提供 + 授权公开主页；或 pending。
5. **Attribution questions and conflicts**：none + 说明不 claim 他人的证明/形式化。

若同条目已有被撤回的旧 issue，在正文注明"替代已撤回的 #NNN"，避免维护者混淆。

---

## 7. 提交后 checklist

- [ ] `manage.py validate` = OK
- [ ] 候选记录 PR 已开，指向正确分支，内容完整
- [ ] `data/*.json` 已再生成并入库；`people/` 档案齐全
- [ ] 收件人已确认（指向授权公开主页）或已用占位符
- [ ] `[Recipient]` issue 已按官方模板提交，只 claim 自己贡献
- [ ] 大日志只存 archive 路径+sha256+bytes，未把私密信息/支付/证件入库
- [ ] 提交包（含适配源码 + lakefile + toolchain + PR 草稿 + 报告）本地留档

## 8. 边界（不要做）

- ❌ 候选记录 `status` 用 `announced` 或自行填 `decision`——候选必须是
  `pending-recipient-confirmation` 且 `decision: null`。
- ❌ 自行把记录迁入 `awards/` 或伪造 `announcement` 链接——**awards/ 迁移由官方维护者**
  按颁奖决定做，需真实 HTTPS 公告链接。你只能停在 `candidates/verified-pending/`。
- ❌ 把 current-release 适配补丁推给仍 pinned 旧 Lean 的上游 repo（会破坏其构建，
  开出的必是失败 PR）。适配版作为可复现产物留在本地提交包即可。
- ❌ 在 commit / title / 附件里放未确认真名或私密信息。
