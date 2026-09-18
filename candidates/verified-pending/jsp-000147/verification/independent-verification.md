# 独立验证说明 — JSP-000147（Erdős Problem #146，Erdős–Simonovits 退化猜想反例）

> 本说明由 jsp147-verifier（aionrs 自动验证运行）出具，用于第三方认证包检查器复核。
> 日期：2026-09-18；验证阶段：D1-B（current-release v4.34 独立重建 + 公理审计）。

## 1. 被验证对象

| 项 | 值 |
|---|---|
| 问题 | Erdős 问题 #146（JSP-000147）：给定二分图 $H$ 限制退化度时 $\operatorname{ex}(n,H)$ 的界（Erdős–Simonovits 退化猜想，https://www.erdosproblems.com/146） |
| 上游仓库 | https://github.com/plby/lean-proofs |
| 上游 pinned commit | `1268917deaaaa0d674f651287027baa26cea9920` |
| 形式化文件 | `src/latest/ErdosProblems/Erdos146.lean`（入口）+ `src/latest/ErdosProblems/Erdos146/`（6 个模块闭包，共 381,239 字节） |
| 数学路径 | Hamming 图 / 熵方法（ten-proofs `CompactnessAndDegeneracy.lean`） |
| 作者 | 解题与形式化：OpenAI ten-proofs（Astra, OpenAI）；pinned 仓库移植：plby（credit，非 claim） |

## 2. 验证环境（current release）

| 项 | 值 |
|---|---|
| Lean 工具链 | `leanprover/lean4:v4.34.0`（当前发布版） |
| mathlib | `v4.34.0`，commit `5ed2965256430c3649e86755f9576b54eca72435` |
| 构建方式 | 源码构建（v4.34.0 无预编译 olean；`MATHLIB_CACHE_DISABLE=1`）；lean.exe 直驱 + 手工 LEAN_PATH（lake 网络校验挂起故不用 lake env） |
| 平台 | Windows 11 x86_64，elan 管理工具链 |
| 验证工程 | `work/jsp-147/verify-current/`（lakefile.lean: `require mathlib @ "v4.34.0"`；模块布局镜像上游 `ErdosProblems/`） |

## 3. 与上游的适配（唯一 1 行移植补丁，已文档化）

1. **上游 pinned 源码为 mathlib v4.33.0 移植版**；在 v4.34.0 上重编译触发
   唯一一处 API 漂移（首轮运行 17:30:47→17:57:45 仅此一错）：
   - `ErdosProblems/Erdos146/BinaryEntropy.lean:2068`：
     `apply Finset.prod_le_prod` → `apply Finset.prod_le_prod₀`。
   - 原因：mathlib 4.34 中 `Finset.prod_le_prod` 新增 `[MulLeftMono N]`
     类型类前提，对 ℝ 不可合成（负标量左乘不单调）；有序环变体
     `prod_le_prod₀` 的前提（每因子 `0 ≤ f i` 与 `f i ≤ g i`）与原证明
     已有的两个分支（`positivity` 与 `choose_le_exp_binary_entropy`）
     完全吻合。
   - 语义不变、不新增公理；源码仅增加 `₀` 的 3 个 UTF-8 字节
     （pinned 103,349 B → as-verified 103,352 B）。
2. 补丁全文、理由与哈希对照见 `PORTING-DIFF.md` 与 `hashes-final.tsv`；
   其余 6 个 Lean 文件与 pinned commit **逐字节一致**。
3. 审计文件 `Audit146.lean` 为本项目自建（import `ErdosProblems.Erdos146`），
   不属上游源码。

## 4. 构建与审计结果

### 构建（run 2，含 1 行补丁；8 步按导入顺序链接）
```
cd work/jsp-147/verify-current
powershell -File compile147.ps1   # BinaryEntropy -> ForbiddenGraph -> HammingProfiles
                                  # -> SamplingAndHammingBalls -> HammingHostAndExclusion
                                  # -> MainTheorem -> Erdos146(entry) -> Audit146
```
结果：**8/8 exit=0**；BinaryEntropy 18:11:33→18:13:54（2m21s），整个闭包
18:11:33→18:15:04（<4 分钟），入口+审计 <20 秒。仅有 deprecated 警告
（`if_neg`/`if_true`），无错误。

### 产物哈希（SHA-256 / bytes，as-verified）
| 文件 | SHA-256 | bytes |
|---|---|---|
| `ErdosProblems/Erdos146.lean`（入口，与 pinned 一致） | `7da2cf47adeb888850f6c85a9b1767949c257b20f62d72fd57f5d4c9cf1763be` | 2760 |
| `ErdosProblems/Erdos146/BinaryEntropy.lean`（含 1 行补丁；pinned=`b4d15290…`/103349） | `164e9dc2028005813190bdcd162423468add976faef145d796cde659c2c32bc3` | 103352 |
| `ErdosProblems/Erdos146/ForbiddenGraph.lean`（与 pinned 一致） | `ace0bb40273b40361bddfdc7f14cdcdd75b42e88cfb157d15b92a061e326664a` | 25620 |
| `ErdosProblems/Erdos146/HammingProfiles.lean`（与 pinned 一致） | `424340071638bfbd648db139d482421dc3968997284d9063d280b65c31124c19` | 88892 |
| `ErdosProblems/Erdos146/SamplingAndHammingBalls.lean`（与 pinned 一致） | `42afbfefb4a376d2f6f79fccb2b3fd17917c6002d74818534893b4ce1468b1da` | 52669 |
| `ErdosProblems/Erdos146/HammingHostAndExclusion.lean`（与 pinned 一致） | `99b7b46e2c2e0ba74219ad6003a638196bbe784dc4c92330879b2e759ae0e748` | 69571 |
| `ErdosProblems/Erdos146/MainTheorem.lean`（与 pinned 一致） | `2301c07afb75beea441fd6cf74f584a168cc37d0910bd34807638e1a4972c911` | 39378 |
| `ErdosProblems/Erdos146.olean`（v4.34.0 编译产物，入口） | `e3804943db9e60ce96e373006cf3359280fa31ae9b0ddd915d66654d3d849c4a` | 188752 |
| 闭包 6 个 `.olean`（BinaryEntropy 5.7MB 最大，合计 ~13MB） | 见 `hashes-final.tsv` | — |
| `current-release-v4.34.log`（构建日志归档） | `93878d4965a3555b80a2f00e135fd33ac6d10be75c2af07a5d66a9345b37f09b` | 4395 |

### 公理审计（`#print axioms`，共 2 个入口定理）
| 定理 | 依赖公理 | 干净 |
|---|---|---|
| `Erdos146.not_erdos_146` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Erdos146.twoDegenerateExtremalCounterexample` | 同上 | ✅ |

仅依赖标准库内置公理，无 `sorryAx`、无用户自定义公理、无 unsafe 声明。

## 5. 复现步骤（检查器）

1. `git clone https://github.com/plby/lean-proofs && git checkout 1268917de`；
2. 取 `src/latest/ErdosProblems/Erdos146.lean` 与
   `src/latest/ErdosProblems/Erdos146/` 全部 6 个 `.lean`；
3. 应用唯一移植补丁（见 `PORTING-DIFF.md`，仅
   `BinaryEntropy.lean:2068` 一行：`prod_le_prod` → `prod_le_prod₀`）；
4. 建立工程：`lean-toolchain` = `leanprover/lean4:v4.34.0`，lakefile 固定
   `require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"`；
5. 按导入顺序 `lean.exe` 编译 7 个文件（或 `lake build`），再编译
   `Audit146.lean`；
6. 尾部 `#print axioms` 输出应与上表一致。

## 6. 与问题陈述的一致性

形式化入口定理 `Erdos146.not_erdos_146` 否定了 Erdős–Simonovits 退化猜想
（∀ r q H, 0<r → 二分 → r-退化 → $\operatorname{ex}(n,H)=O(n^{2-1/r})$ 不成立），
与问题 #146 所问（二分图限制退化度时 $\operatorname{ex}(n,H)$ 是否至多
$n^{2-1/r+o(1)}$）的正确答案（**否**，Bukh–Conlon 式反例）一致；
`Erdos146.twoDegenerateExtremalCounterexample` 显式构造反例：连通二分
2-退化 Hamming 图 $H$ 与 $c,\varepsilon>0$，
$\operatorname{ex}(n,H)\ge c\,n^{3/2+\varepsilon}$ 最终成立，严格超过
推测界 $O(n^{3/2})$。详见 `verification/statement.yaml`，`result: equivalent`。

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

- 移植补丁：`PORTING-DIFF.md`；哈希表：`hashes-final.tsv`
- 验证日志：`verification/current-release-v4.34.log`
- 元数据：`award.yaml`、`citation.md`、`recipients.md`、`verification/record.yaml`
- 本说明落盘：`verification/independent-verification.md`