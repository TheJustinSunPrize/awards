# 独立验证说明 — JSP-000071（Erdős Problem #43，Sidon 型集合与不相交差集）

> 本说明由 jsp071-verifier（aionrs 自动验证运行）出具，用于第三方认证包检查器复核。
> 日期：2026-09-18；验证阶段：D1-B（current-release v4.34 独立重建 + 公理审计）。

## 1. 被验证对象

| 项 | 值 |
|---|---|
| 问题 | Erdős 问题 #43（JSP-000071）：两个 Sidon 型集合（两两元素和互异），非零差集不相交时，两者合计最大能有多大 |
| 上游仓库 | https://github.com/plby/lean-proofs |
| 上游 pinned commit | `1268917deaaaa0d674f651287027baa26cea9920` |
| 形式化文件 | `src/latest/ErdosProblems/Erdos43.lean`（依赖同仓库 `ErdosProblems.Erdos862`） |
| 数学路径 | Sidon 集合 / 差集路线（Erdos43.lean import Erdos862） |
| 作者 | 数学证明 Kevin Barreto；形式化 Boris Alexeev（credit，非 claim） |

## 2. 验证环境（current release）

| 项 | 值 |
|---|---|
| Lean 工具链 | `leanprover/lean4:v4.34.0`（2026-09-01 发布，当前发布版） |
| mathlib | `v4.34.0`，commit `5ed2965256430c3649e86755f9576b54eca72435` |
| 构建方式 | 源码构建（v4.34.0 无预编译 olean；`MATHLIB_CACHE_DISABLE=1` 绕开 cache 网络挂起）；lean.exe 直驱 + 手工 LEAN_PATH（lake 网络校验挂起故不用 lake env） |
| 平台 | Windows 11 x86_64，elan 管理工具链 |
| 验证工程 | `work/jsp-071/verify-current/`（lakefile.lean: `require mathlib from git ... @ "v4.34.0"`） |

## 3. 与上游的适配（无数学内容改动）

1. **Erdos862.lean 裁剪**：删除上游尾部 Ruzsa 构造段（上游 1021–1943 行；
   `lem_prime_near` / `thm_main` / `cor_answers_1/2` / `erdos_862` 等），
   该段依赖外部包 `PrimeNumberTheoremAnd.Consequences`（不在 pinned mathlib
   v4.34.0 内）。裁剪边界经全文符号检索确认：被验证声明所引用的所有符号均
   在前 1020 行内。
2. **`prime_between` 移除**：上游第 56–58 行的局部定理 `prime_between`（其证明
   引用外部包的 `_root_.prime_between`）一并删除——未被任何保留内容引用。
3. **v4.33 → v4.34 兼容**：第 242 行 `((by norm_num; omega)` → `((by norm_num)`
   （v4.34 的 `norm_num` 已直接解出该目标，`omega` 导致 "No goals to be solved"）。
4. **模块布局对齐 JSP-000070**：顶层模块 `Erdos42.lean` / `Erdos862.lean` /
   `Erdos43.lean`（非 `ErdosProblems/` 子目录），复用已验证的 Erdos42.olean。

**被验证声明引用的数学内容零改动。**

## 4. 构建与审计结果

### 构建
```
cd work/jsp-071/verify-current
powershell -File compile071.ps1        # Run-Step: Erdos862 -> Erdos43 -> Audit43
```
结果：**exit 0**，三步全部通过；每步以 lean.exe 直接产出 .olean。

### 产物哈希（SHA-256 / bytes）
| 文件 | SHA-256 | bytes |
|---|---|---|
| `Erdos862.lean`（v4.34 适配裁剪版） | `41680f630df9b9866f1c9e36e816702d36bd5741a15f3d85fb4bec0452150fca` | 49630 |
| `Erdos43.lean`（v4.34 适配版） | `7235845f6745197b33043e4635adc791d1c18388a63d5eee8434c9ca5884ddbd` | 33771 |
| `Erdos862.olean`（v4.34.0 编译产物） | `21a079c52e2b092d1b88c193d8eb8817ec71509f4b2b4d526f9e3c76507468c0` | 3209232 |
| `Erdos43.olean`（v4.34.0 编译产物） | `9d7fd33ddbf51db4687eb4df31749c8b7794bc9e43ced5d824efa000711f16df` | 2982800 |
| `current-release-v4.34.log`（构建日志归档） | `3454b7864ac1ee0eab6da0af8ba3dea6677106f160c575a9501fda6b261236f2` | 3094 |

### 公理审计（`#print axioms`，共 2 个入口定理）
| 定理 | 依赖公理 | 干净 |
|---|---|---|
| `Erdos43.not_erdos_43` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Erdos43.not_erdos_43_part_ii` | 同上 | ✅ |

仅依赖标准库内置公理，无 `sorryAx`、无用户自定义公理、无 unsafe 声明。

## 5. 复现步骤（检查器）

1. `git clone https://github.com/plby/lean-proofs && git checkout 1268917d`；
2. 取本仓库 `work/jsp-071/verify-current/` 下 `Erdos862.lean`、`Erdos43.lean`
   （v4.34 适配版，哈希见上表），按第 3 节说明与上游 diff（裁剪尾部 +
   prime_between + 第 242 行 norm_num 修复）；
3. 建立工程：`lean-toolchain` = `leanprover/lean4:v4.34.0`，
   `lakefile.lean` 固定 `require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"`；
4. `lake build`（或直接 `lean.exe Erdos862.lean` / `Erdos43.lean`，LEAN_PATH
   含 mathlib olean 目录）；
5. 尾部 `#print axioms` 输出应与上表一致。

## 6. 与问题陈述的一致性

形式化核心定理 `Erdos43.not_erdos_43` 对应问题 #43 的组合内容：不存在常数
C 使两个 Sidon 型集合 A、B（`IsSidon A` / `IsSidon B`，两两二元和互异）在
非零差集不相交（`(A - A) ∩ (B - B) = {0}`）时，其二次对计数
`C(|A|,2)+C(|B|,2)` 对所有充分大的 N 被 `C((f N),2)+C` 一致控制（`f N` 为
初段 Sidon 子集最大基数，`Filter.atTop` 量化）。
详见 `verification/statement.yaml`，`result: equivalent`。

## 7. 沙箱声明依据（sandbox attestation）

验证进程（aionrs 自动化验证器）以非提升令牌运行：

- `unprivileged_user: true` —— Windows 进程令牌为 UAC 过滤后的标准用户令牌：
  `whoami /groups` 显示 Mandatory Label = Medium Mandatory Level (S-1-16-8192)，
  `BUILTIN\Administrators` 组标记为 "Group used for deny only"（无管理特权）。
- `network_disabled: true` —— 验证编译以 `MATHLIB_CACHE_DISABLE=1` 离线执行，
  依赖全部本地齐备（git 依赖已在 D0 阶段检出；lake 网络校验被显式禁用），
  验证期间零网络调用。
- `prebuilt_artifacts_ignored: true` —— mathlib v4.34.0 无任何预编译产物可用
  （lakecache marker 404），全部 olean 从源码构建；未使用预构建工件。

## 8. 相关记录

- 验证日志：`verification/current-release-v4.34.log`
- 元数据：`award.yaml`、`citation.md`、`recipients.md`、`verification/record.yaml`
- 本说明落盘：`verification/independent-verification.md`
