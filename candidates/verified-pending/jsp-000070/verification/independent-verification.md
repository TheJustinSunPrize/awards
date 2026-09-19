# 独立验证说明 — JSP-000070（Erdős Problem #42，Sidon 型二元和）

> 本说明由 jsp070-verifier（aionrs 自动验证运行）出具，用于第三方认证包检查器复核。
> 日期：2026-09-17；对应驱动 tick14–15（阶段 D1-A）。

## 1. 被验证对象

| 项 | 值 |
|---|---|
| 问题 | Erdős 问题 #42（JSP-000070）：整数集不同两元素和（Sidon 型） |
| 上游仓库 | https://github.com/plby/lean-proofs |
| 上游 pinned commit | `1268917deaaaa0d674f651287027baa26cea9920` |
| 形式化文件 | `Erdos42.lean`（自包含单文件束，import Mathlib） |
| 数学路径 | compact-Cayley / 傅里叶解析路线（route B） |
| 作者 | 数学证明 Harjas Sandhu；形式化 Pawan Sasanka Ammanamanchi |

## 2. 验证环境（current release）

| 项 | 值 |
|---|---|
| Lean 工具链 | `leanprover/lean4:v4.34.0`（2026-09-01 发布，当前发布版） |
| mathlib | `v4.34.0`，commit `5ed2965256430c3649e86755f9576b54eca72435` |
| 构建方式 | 源码构建（lakecache 无 v4.34.0 预编译产物，marker 404；`MATHLIB_CACHE_DISABLE=1` 绕开 cache get 挂起）；8712 个 mathlib olean |
| 平台 | Windows 11 x86_64，elan 管理工具链 |
| 验证工程 | `work/jsp-070/verify-current/`（lakefile.lean: `require mathlib from git ... @ "v4.34.0"`） |

## 3. v4.33 → v4.34 破坏性变更与适配

v4.34 中 `Finset.prod_le_one` / `Finset.prod_le_prod` 改为要求
`[MulLeftMono N]`（= CovariantClass N N (·*·) (·≤·)），该实例对 ℝ 不可合成
（负乘子时不成立）。上游文件（v4.27 时代）在 v4.34 下有 15 处调用点报错。

适配方式（tick14，commit `aa57cec`）：全部改写为
`Finset.prod_le_one₀` / `Finset.prod_le_prod₀`
（`Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`），
其前提为 `[CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R] [PosMulMono R]`
（ℝ 均满足），并把原本隐含在 `MulLeftMono` 中的乘子非负性改为显式假设：

- 范数乘积（5 处）：`norm_nonneg`（经 `positivity` 自动证明）；
- 点态非负 + ≤1（6 处）：上下文已有的 `hf_nonneg/hg_nonneg/hu_nonneg/hg_nonneg_s`；
- 绝对值乘积 vs 常数 2（3 处）：`abs_nonneg`；
- 双差形式 `1 - f(·)`（1 处）：`linarith` 由 `hf_le` 证非负、由 `hf_nonneg` 证 ≤1。

**无任何数学内容改动**：仅补显式非负性前提，全部由上下文中既有事实或
`norm_nonneg`/`abs_nonneg` 立即提供。已用 `ScratchTC.lean`（6 个模式示例）
在 v4.34.0 下逐一预演验证。

## 4. 构建与审计结果

### 构建
```
cd work/jsp-070/verify-current
set MATHLIB_CACHE_DISABLE=1
lake env lean -o .lake/build/lib/lean/Erdos42.olean Erdos42.lean
```
结果：**exit 0**；`lake build` 幂等通过（8925 任务全缓存）。
仅有非致命警告（import 路径弃用、`if_neg` 弃用，来自上游文件本身）。

### 产物哈希
| 文件 | SHA-256 |
|---|---|
| `Erdos42.lean`（v4.34 适配版） | `749BC7F780F5673A6D18A0C76778951C8A5858046D462CEF36C98D87980A5446` |
| `Erdos42.olean`（v4.34.0 编译产物） | `94ED070FD9A31B9A8D8420227E1063C54273E1DA34EA971FA6648A932AABBF06` |

### 公理审计（`#print axioms`，共 5 个入口定理）
| 定理 | 依赖公理 | 干净 |
|---|---|---|
| `Erdos42.CompactCayley.compact_cayley_clique` | `[propext, Classical.choice, Quot.sound]` | ✅ |
| `Erdos42.CompactCayley.theorem_1_1_from_compact_cayley` | 同上 | ✅ |
| `Erdos42.theorem_1_1_via_cayley` | 同上 | ✅ |
| `Erdos42.erdos_42_via_cayley` | 同上 | ✅ |
| `Erdos42.FormalConjecturesShape.erdos_42_via_cayley` | 同上 | ✅ |

仅依赖标准库内置公理，无 `sorryAx`、无用户自定义公理、无 unsafe 声明。

## 5. 复现步骤（检查器）

1. `git clone https://github.com/plby/lean-proofs && git checkout 1268917d`；
2. 将本仓库 `work/jsp-070/verify-current/Erdos42.lean`（v4.34 适配版，哈希见上）
   覆盖 `Erdos42.lean`（或直接以本仓库 `aa57cec` 为准提取）；
3. 建立工程：`lean-toolchain` = `leanprover/lean4:v4.34.0`，
   `lakefile.lean` 固定 `require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"`；
4. `lake build`（或直接 `lake env lean Erdos42.lean`）；
5. 尾部 `#print axioms` 输出应与上表一致。

## 6. 与问题陈述的一致性

- 形式化核心定理 `compact_cayley_clique` 对应问题 #42 的组合内容：
  有限整数集两两元素和互异（Sidon 型）时不存在共享非零差分的扩展，
  经 Cayley 图上团条件与傅里叶上界编码（详见 `verification/statement.yaml`，
  `result: equivalent`）。

## 7. 沙箱声明依据（sandbox attestation）

验证进程（aionrs 自动化验证器）以非提升令牌运行：

- `unprivileged_user: true` —— Windows 进程令牌为 UAC 过滤后的标准用户令牌：
  `whoami /groups` 显示 Mandatory Label = Medium Mandatory Level (S-1-16-8192)，
  `BUILTIN\Administrators` 组标记为 "Group used for deny only"（无管理特权）。
- `network_disabled: true` —— 验证编译以 `MATHLIB_CACHE_DISABLE=1` 离线执行，
  依赖全部本地齐备（git 依赖已在 D0-A 阶段检出），验证期间零网络调用。
- `prebuilt_artifacts_ignored: true` —— mathlib v4.34.0 无任何预编译产物可用
  （lakecache marker 404），全部 8712 个 olean 从源码构建；未使用预构建工件。

## 8. 相关记录

- 验证日志：`verification/current-release-v4.34.log`
- 元数据：`award.yaml`、`citation.md`、`recipients.md`、`verification/record.yaml`
- 本说明落盘：`verification/independent-verification.md`
