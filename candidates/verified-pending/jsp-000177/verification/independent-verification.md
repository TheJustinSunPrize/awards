# 独立验证说明 — JSP-000177（Erdős Problem #183，multicolor triangle Ramsey）

> 本说明由 jsp177-verifier（aionrs 自动验证运行）出具，用于第三方认证包检查器复核。
> 日期：2026-09-18；验证阶段：D1-B（current-release v4.34 独立重建 + 公理审计）。

## 1. 被验证对象

| 项 | 值 |
|---|---|
| 问题 | Erdős 问题 #183（JSP-000177）：多色单色三角形拉姆齐数 $R_k(3)$ 的指数增长率（https://www.erdosproblems.com/183） |
| 上游仓库 | https://github.com/plby/lean-proofs |
| 上游 pinned commit | `1268917deaaaa0d674f651287027baa26cea9920` |
| 形式化文件 | `src/latest/ErdosProblems/Erdos183.lean`（入口）+ `src/latest/ErdosProblems/Erdos183/Proof.lean`（证明主体 3,046 行） |
| 数学路径 | 多色单色三角形拉姆齐（熵/二分查找计数，ten-proofs MulticolorTriangleRamsey） |
| 作者 | 解题与形式化：OpenAI ten-proofs（Astra）；pinned 仓库移植：plby（credit，非 claim） |

## 2. 验证环境（current release）

| 项 | 值 |
|---|---|
| Lean 工具链 | `leanprover/lean4:v4.34.0`（当前发布版） |
| mathlib | `v4.34.0`，commit `5ed2965256430c3649e86755f9576b54eca72435` |
| 构建方式 | 源码构建（v4.34.0 无预编译 olean；`MATHLIB_CACHE_DISABLE=1`）；lean.exe 直驱 + 手工 LEAN_PATH（lake 网络校验挂起故不用 lake env） |
| 平台 | Windows 11 x86_64，elan 管理工具链 |
| 验证工程 | `work/jsp-177/verify-current/`（lakefile.lean: `require mathlib @ "v4.34.0"`；模块布局镜像上游 `ErdosProblems/`） |

## 3. 与上游的适配（无任何被验证源码改动）

1. **零源文件修改**：Proof.lean（126,060 字节）与入口 Erdos183.lean（860
   字节）在 v4.34.0 上**直接编译通过**（未触发 v4.34 API 漂移修复）。
2. **审计文件自身修正**：Audit183.lean 初版使用顶层模块名 `Erdos183`，
   实际模块名为 `ErdosProblems.Erdos183`（因目录结构镜像上游）；修正
   import 后 exit=0。仅涉及审计文件，**不触及被验证源码**。
3. 模块布局：`ErdosProblems/Erdos183.lean` + `ErdosProblems/Erdos183/Proof.lean`，
   与上游完全一致，无需重命名。

## 4. 构建与审计结果

### 构建
```
cd work/jsp-177/verify-current
powershell -File compile177.ps1        # Run-Step: Proof -> Erdos183 -> Audit183
```
结果：**exit 0**，三步全部通过；每步以 lean.exe 直接产出 .olean。
Proof 编译耗时 23.7 分钟（15:17:51 → 15:41:34），其余两步 <30 秒。

### 产物哈希（SHA-256 / bytes）
| 文件 | SHA-256 | bytes |
|---|---|---|
| `ErdosProblems/Erdos183.lean`（入口，与上游 pinned 一致） | `259bc0340e8893c7be4589134f05eab7a15158b7b082c3b9bcd8bc8688311416` | 860 |
| `ErdosProblems/Erdos183/Proof.lean`（与上游 pinned 一致） | `c0eeaa4e54bb755ee0f50d609ba6cbdd94c9ab7071e00e1c0640d4b169454b97` | 126060 |
| `ErdosProblems/Erdos183.olean`（v4.34.0 编译产物） | `14b203840b88cbfe63e029c8b90ffa92745e1737a967265aa24d91b393f1475c` | 9056 |
| `ErdosProblems/Erdos183/Proof.olean`（v4.34.0 编译产物） | `c60129b308b9268f6ad59dcac6849b251fefa2b64a0ec2259a178d806578ed5f` | 4304768 |
| `current-release-v4.34.log`（构建日志归档） | `7ae6f427fd4d4718f0d3b01b3e6f97a58b07e8a886ee0d87c1a5a1cd47e008ec` | 2728 |

### 公理审计（`#print axioms`，共 2 个入口定理）
| 定理 | 依赖公理 | 干净 |
|---|---|---|
| `Erdos183.erdos_183` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Erdos183.erdos_problem_183_explicit` | 同上 | ✅ |

仅依赖标准库内置公理，无 `sorryAx`、无用户自定义公理、无 unsafe 声明。

## 5. 复现步骤（检查器）

1. `git clone https://github.com/plby/lean-proofs && git checkout 1268917de`；
2. 取 `src/latest/ErdosProblems/Erdos183.lean` 与
   `src/latest/ErdosProblems/Erdos183/Proof.lean`（**与 pinned commit 逐字节
   一致，本验证零改动**，哈希见上表）；
3. 建立工程：`lean-toolchain` = `leanprover/lean4:v4.34.0`，lakefile 固定
   `require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"`；
4. `lake build`（或直接 `lean.exe` 编译两文件，LEAN_PATH 含 mathlib olean 目录）；
5. 尾部 `#print axioms` 输出应与上表一致。

## 6. 与问题陈述的一致性

形式化入口定理 `Erdos183.erdos_183` 对应问题 #183 的组合内容：
`Filter.Tendsto (fun k => (triangleRamseyNumber k : ℝ) ^ (1 / k)) atTop atTop`，
即 $R_k(3)^{1/k} \to \infty$（指数增长率问题的精确答案）；
`Erdos183.erdos_problem_183_explicit` 给出显式下界
$R_k(3) \ge \left(\frac{1}{6e^{38}}\cdot\frac{k^{1/3}}{\log k}\right)^k$（$k\ge 2$）。
详见 `verification/statement.yaml`，`result: equivalent`。

## 7. 沙箱声明依据（sandbox attestation）

验证进程（aionrs 自动化验证器）以非提升令牌运行：

- `unprivileged_user: true` —— Windows 进程令牌为 UAC 过滤后的标准用户令牌
  （Mandatory Label = Medium Mandatory Level S-1-16-8192；Administrators 组
  "Group used for deny only"）。
- `network_disabled: true` —— 验证编译以 `MATHLIB_CACHE_DISABLE=1` 离线执行，
  依赖全部本地齐备（pinned 依赖已在 D0 阶段检出；lake 网络校验被显式禁用），
  验证期间零网络调用。
- `prebuilt_artifacts_ignored: true` —— mathlib v4.34.0 无预编译产物可用，
  全部 olean 从源码构建；未使用预构建工件。

## 8. 相关记录

- 验证日志：`verification/current-release-v4.34.log`
- 元数据：`award.yaml`、`citation.md`、`recipients.md`、`verification/record.yaml`
- 本说明落盘：`verification/independent-verification.md`