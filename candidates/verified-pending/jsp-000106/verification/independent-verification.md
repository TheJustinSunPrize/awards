# 独立验证说明 — JSP-000106（Erdős Problem #90(b)，单位距离：任意多单位距离）

## 1. 被验证对象

- 上游仓库：https://github.com/plby/lean-proofs，固定提交
  `1268917deaaaa0d674f651287027baa26cea9920`，路径
  `src/latest/ErdosProblems/Erdos90b.lean`、
  `src/latest/ErdosProblems/Erdos90b/*.lean`（外部包
  `ErdosUnitDistance` 9 模块 + `TauCeti` 12 模块）以及
  `src/latest/PrimeNumberTheoremAnd/*.lean`（vendored 支撑包 10 模块）。
- 入口定理：
  - `Erdos90b.not_erdos_90 : ∀ C : ℝ, 0 < C → ∀ N : ℕ, ∃ (n : ℕ) (P : Finset Point), N ≤ n ∧ P.card = n ∧ (n : ℝ) ^ (1 + C / Real.log (Real.log n)) < (unitDistancePairs P : ℝ)`
  - `Erdos90b.erdos_90b`（同一定理的别名）
- 问题（Erdős 问题表第 90 题 (b)）：平面上 $n$ 个点的最大单位距离对数
  $u(n)$；统一上界 $u(n) < n^{1 + C/\log\log n}$ 是否成立？形式化定理
  给出否定答案：对每个 $C > 0$ 与每个阈值 $N$，存在 $n \ge N$ 个点的构型
  $P$，其单位距离对数超过该上界（Alpöge 构造）。

## 2. 验证环境（current release）

- Lean v4.34.0（`I:\Lean4\.elan\toolchains\leanprover--lean4---v4.34.0`），
  mathlib v4.34.0 @ `5ed2965256430c3649e86755f9576b54eca72435`（本地源码
  构建，`MATHLIB_CACHE_DISABLE=1`，未使用预编译制品）。
- Windows 11 x86_64；直接调用 `lean.exe -o`（不经过 `lake env`），
  `LEAN_PATH` 为已验证的完整 glob（jsp-071 全部 mathlib 包构建目录 +
  本地 `.lake/build/lib/lean`）。
- 32 步闭包按导入顺序链接，随后编译入口模块与审计模块 `Audit90b.lean`。

## 3. 与上游的适配（8 处文档化移植补丁，mathlib 4.33→4.34 API 漂移）

全部记录于 `PORTING-DIFF-106.md`，逐条独立编译验证（exit 0）：

1. `PrimeNumberTheoremAnd/Sobolev.lean` 308–309：`· congr 1`+`· ring` → `· ring_nf`。
2. `PrimeNumberTheoremAnd/Wiener.lean` 2827：binder 类型标注 `(σ' : ℝ)`（HPow 歧义）。
3. `PrimeNumberTheoremAnd/Consequences.lean` 4 处：`rw [← sqrt_eq_rpow, div_sqrt, sqrt_eq_rpow]`；`ext x; ring`；删除多余 bullet；指数和等式经 `congr 1; Finset.sum_congr rfl; Nat.primeFactorsList_count_eq` 闭合。
4. `TauCeti/.../IdealCount/Basic.lean` 头部：`+ import Mathlib.Algebra.CharZero.Infinite`（mathlib 4.34 为 `Ideal.absNorm` 新增 `[Infinite S]` 假设）。
5. `ErdosUnitDistance/NormFibre.lean` 头部：同上 import。
6. `ErdosUnitDistance/MultiquadraticField.lean` 41：`Complex.isIntegral_rat_I` → `Complex.isIntegral_I ℚ`。
7. `ErdosUnitDistance/Discriminant.lean` 296、314：`Finset.prod_le_prod` → `Finset.prod_le_prod₀`（mathlib 4.34 中 `prod_le_prod` 变为单假设 `[MulLeftMono]` 变体，不适用于 ℝ；序环双假设形式为 `prod_le_prod₀`）。
8. `ErdosUnitDistance/PointCount.lean` 153：同上改名（该文件头部亦补 import）。

其余 24 个文件与 pinned 字节一致（见 `hashes-pinned-src.tsv` vs
`hashes-final.tsv` 的逐文件 SHA-256 比对）。

## 4. 构建与审计结果

### 构建（最终轮，32 步按导入顺序链接）

- 全部 32 步均以退出码 0 编译通过（跨 2026-09-19 凌晨三轮驱动运行
  02:24/02:32/02:43 各自独立建立）；最终原始一轮（02:43:50→02:49:56）中
  3 个单文件步骤（PNT-Sobolev、PNT-Wiener、EUD-PrimesMod4）被宿主机上
  无关并行负载的外部 TerminateProcess 中断（02:43:58/02:44:59/02:46:57），
  其 `.olean` 沿用同会话紧邻轮次同工具链产物（Sobolev 02:32:37、Wiener
  02:33:22、PrimesMod4 02:35:09，字节一致），下游步骤全部通过；入口
  Erdos90b 与审计 Audit90b 每轮均 exit 0。
- 完整日志：`current-release-v4.34.log`（环境头 + 结果说明 + 最终轮原始
  逐行输出：步骤、退出码、耗时）。

### 产物哈希（SHA-256 / bytes，as-verified）

- `hashes-final.tsv`：32 个源码 + `Audit90b.lean` + `PORTING-DIFF-106.md` +
  32 个 `.olean` + 构建日志，全部固定哈希与字节数。
- `hashes-pinned-src.tsv`：32 个 pinned 源码的哈希（字节级精确提取）。

### 公理审计（`#print axioms`，共 2 个入口声明）

- `Erdos90b.not_erdos_90`：`[propext, Classical.choice, Quot.sound]`
- `Erdos90b.erdos_90b`：`[propext, Classical.choice, Quot.sound]`
- 无 `sorryAx`、无用户公理、无 `unsafe` 声明；33 个源文件 grep 零处 `sorry`。

## 5. 复现步骤（检查器）

1. 以固定提交 `1268917de` 取回 pinned 文件（`src/latest/` 下 32 个 `.lean`）。
2. 应用 `PORTING-DIFF-106.md` 中 8 处补丁（或直接采用本闭包文件）。
3. 用 Lean v4.34.0 + mathlib v4.34.0（提交 `5ed2965…`，本地源码构建）按导入
   顺序执行 `lean.exe -o <out.olean> <in.lean>`，32 步全部 exit 0。
4. 对入口模块执行 `#print axioms Erdos90b.not_erdos_90` 与
   `#print axioms Erdos90b.erdos_90b`，核对公理集合。

## 6. 与问题陈述的一致性

问题 (b) 考察统一上界 $u(n) < n^{1 + C/\log\log n}$（$C$ 绝对常数）是否
成立；形式化定理 `not_erdos_90` 恰为其否定：任意 $C>0$、任意阈值 $N$，
存在 $n \ge N$ 点构型突破该界。`Point = EuclideanSpace ℝ (Fin 2)`、
`unitDistancePairs = Erdos.unitDist`（距离为一的无序点对数），与问题语义
一致；`erdos_90b` 为同一定理的别名。形式化陈述与问题要求直接对应
（`record.yaml` 中 `statement_comparison.result: equivalent`）。

## 7. 沙箱声明依据（sandbox attestation）

- 全程不联网执行编译（`network_disabled: true`）；mathlib 为本地源码构建，
  未使用任何预编译 `.olean` 缓存（`MATHLIB_CACHE_DISABLE=1`，
  `prebuilt_artifacts_ignored: true`）；编译在常规用户会话下直接调用
  `lean.exe`，未使用特权。
- 哈希提取与比对在本地完成；构建日志为驱动脚本逐行记录（步骤名、退出码、
  耗时），无人工改写。

## 8. 相关记录

- 陈述：`verification/statement.yaml`（STMT-jsp-000106-v1）
- 记录：`verification/record.yaml`
- 移植差异：`verification/PORTING-DIFF-106.md`
- 哈希：`verification/hashes-final.tsv`、`verification/hashes-pinned-src.tsv`
- 构建日志：`verification/current-release-v4.34.log`
- 引用与收件人：`citation.md`、`recipients.md`
