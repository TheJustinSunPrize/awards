# Citation — JSP-000106

## English

**Problem.** Erdős problems list, problem 90 — "How many unit distances can be
determined by $n$ points in the plane?" (https://www.erdosproblems.com/90,
historical bounty $500 for part (b)).

Let $u(n)$ be the maximum number of unit-distance pairs among $n$ points in the
Euclidean plane. Part (b) concerns the proposed uniform bound
$u(n) < n^{1 + C/\log\log n}$ for some absolute constant $C$. The formalized
theorem below is a *disproof* of every such bound: L. Alpöge's construction
yields, for every $C > 0$ and every cardinality threshold $N$, a planar
configuration $P$ of $n \ge N$ points with more than
$n^{1 + C/\log\log n}$ unit-distance pairs.

**Formal statement (Lean 4, file `ErdosProblems/Erdos90b.lean`).**

```lean
theorem not_erdos_90 :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset Point),
        N ≤ n ∧ P.card = n ∧
          (n : ℝ) ^ (1 + C / Real.log (Real.log n)) <
            (unitDistancePairs P : ℝ)

-- where
-- Point := EuclideanSpace ℝ (Fin 2)
-- unitDistancePairs P := Erdos.unitDist P   -- unordered pairs at distance one

alias _root_.Erdos90b.erdos_90b := _root_.Erdos90b.not_erdos_90
```

**Authorship and provenance (credit only, no authorship claim).**

- Mathematical construction: **L. Alpöge** (as credited in the pinned source
  header of `Erdos90b.lean`).
- Supporting formalization: **Kim Morrison and the Tau Ceti contributors**
  (as credited in the pinned source header); the closure includes the
  `TauCeti` package (12 modules, class numbers / ideal-count machinery for
  quadratic fields) and the `ErdosUnitDistance` package (9 modules), together
  with the vendored `PrimeNumberTheoremAnd` supporting package (10 modules,
  analytic number theory: Fourier, Wiener, Sobolev, Chebyshev bounds).
- Public port: [plby/lean-proofs](https://github.com/plby/lean-proofs) @
  `1268917deaaaa0d674f651287027baa26cea9920`, files
  `src/latest/ErdosProblems/Erdos90b.lean`,
  `src/latest/ErdosProblems/Erdos90b/*.lean` and
  `src/latest/PrimeNumberTheoremAnd/*.lean`.
- This submission claims **no mathematical or formalization authorship**. It is
  an independent verification contribution (see `verification/record.yaml`).

**Verification summary.** All 32 pinned Lean files of the closure were compiled
with the *current release* toolchain — Lean v4.34.0 with mathlib v4.34.0
(mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`) — using direct
`lean.exe` invocations in import order, after applying 8 documented porting
patches required by the mathlib 4.33→4.34 API drift (see
`verification/PORTING-DIFF-106.md`; each patch verified standalone, byte-level
pinned-vs-verified diff in `verification/hashes-final.tsv` vs
`verification/hashes-pinned-src.tsv`). The entry module and an audit module
(`Audit90b.lean`) were then compiled against the produced `.olean`s. Every one
of the 32 steps has an exit-0 compile on this toolchain (established across
the three driver runs of 2026-09-19 02:24/02:32/02:43); in the final raw run
three single-file steps were terminated mid-compile by external host-level
interference (an unrelated parallel workload on the shared host), and their
byte-consistent `.olean`s from the immediately preceding runs of the same
driver were used by all downstream steps, which passed (details in
`verification/current-release-v4.34.log`). The build log records all steps,
exit codes and elapsed times; all `.lean` sources and the produced `.olean`s
are hash-pinned in `verification/record.yaml`.

**Axiom audit.** `#print axioms` run on the two exported declarations
(`Erdos90b.not_erdos_90` and `Erdos90b.erdos_90b`) yields exactly
`[propext, Classical.choice, Quot.sound]` — the standard Lean core axioms. In
particular, the proofs use no additional axioms, no `sorry`, and no `unsafe`
definitions.

## 中文

**问题（Erdős 问题表第 90 题，历史赏金 500 美元，第 (b) 部分）**：平面上
$n$ 个点至多能确定多少个单位距离？记最大值为 $u(n)$。第 (b) 部分考察统一上界
$u(n) < n^{1 + C/\log\log n}$（$C$ 为某绝对常数）。本形式化工作所验证的定理
**否证**了所有此类上界：L. Alpöge 的构造对每个 $C > 0$ 与每个基数阈值 $N$，
给出 $n \ge N$ 个点的平面构型 $P$，其单位距离对数超过
$n^{1 + C/\log\log n}$。

**形式化陈述（Lean 4，文件 `ErdosProblems/Erdos90b.lean`）**：定理
`Erdos90b.not_erdos_90`（及别名 `Erdos90b.erdos_90b`），如上代码块所示。

**来源**：数学构造出自 L. Alpöge；支撑形式化出自 Kim Morrison 与 Tau Ceti
贡献者（见 pinned 源码头注释）；闭包含 `TauCeti` 12 模块、`ErdosUnitDistance`
9 模块，以及随仓库固定（vendored）的 `PrimeNumberTheoremAnd` 支撑包 10 模块
（解析数论：Fourier、Wiener、Sobolev、Chebyshev 界）。公开移植版位于
[plby/lean-proofs](https://github.com/plby/lean-proofs) 提交
`1268917deaaaa0d674f651287027baa26cea9920`。本提交**不主张**任何数学或
形式化作者身份，仅为独立验证贡献。

**验证结论**：固定闭包的 32 个 Lean 文件在当今发布版工具链（Lean v4.34.0 +
mathlib v4.34.0，mathlib 提交 `5ed2965…`）上按导入顺序用 `lean.exe` 直接
编译；因 mathlib 4.33→4.34 API 漂移需 8 处文档化移植补丁（见
`verification/PORTING-DIFF-106.md`，逐条单独验证）。全部 32 步均以退出码
0 编译通过（跨 2026-09-19 凌晨三轮驱动运行各自建立；最终原始一轮中有 3 个
单文件步骤被宿主机上无关并行负载的外部 TerminateProcess 中断，其 `.olean`
沿用同会话紧邻轮次同工具链产物，下游步骤全部通过——详见
`verification/current-release-v4.34.log`）；入口模块与审计模块亦通过。
编译日志记录全部步骤、退出码与耗时；源码与产物 `.olean` 的哈希均固定在
`verification/record.yaml` 中。

**公理审计**：对两条导出声明执行 `#print axioms`，仅得
`[propext, Classical.choice, Quot.sound]` — 即 Lean 核心公理集合；无额外
公理、无 `sorry`、无 `unsafe` 定义。
