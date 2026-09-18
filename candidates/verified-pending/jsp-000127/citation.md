# Citation — JSP-000127

## English

**Problem.** Erdős problems list, problem 119 — "If all zeros of a polynomial
lie on the unit circle, how does its maximum modulus on the prescribed region
grow with its degree?" (https://www.erdosproblems.com/119, historical bounty
$100).

Let $p_n(z) = \prod_{i < n}(z - z_i)$ be a monic polynomial of degree $n$ whose
zeros all lie on the unit circle ($|z_i| = 1$), and let
$M_n = \max_{|z|=1} |p_n(z)|$ be its maximum modulus on the unit circle — the
prescribed region. The problem asks how $M_n$ can grow with the degree $n$. The
formalized theorems below answer this growth question for every sequence of
roots on the unit circle:

- `Erdos119.erdos_119` — there is an absolute constant $c > 0$
  ($c = 1/256$ in the proof) such that eventually in $n$,
  $\sum_{k<n} M_k > n^{1+c}$;
- `Erdos119.erdos_119.parts.iii_quantitative` — eventually
  $C \cdot n^{5/4}/\sqrt{\log n} < \sum_{k<n} M_k$ for some constant $C > 0$;
- `Erdos119.erdos_119.parts.ii` — $M_n > n^c$ for infinitely many $n$;
- `Erdos119.erdos_119.parts.i` — $\limsup_n M_n = \infty$.

**Formal statements (Lean 4, file `ErdosProblems/Erdos119.lean`, module
`ErdosProblems.Erdos119`, namespace `Erdos119`).**

```lean
theorem erdos_119 (z : ℕ → ℂ) :
    (∀ i, ‖z i‖ = 1) →
      ∃ c, ∃ (_ : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ Finset.range n, M z k > (n : ℝ) ^ (1 + c)

-- M z n := sSup {‖p z n w‖ | w : ℂ, ‖w‖ = 1}   (maximum modulus on the unit circle)
-- p z n := ∏ i ∈ Finset.range n, (w - z i)     (the polynomial whose zeros are z 0 … z (n-1))
```

**Authorship and provenance (credit only; this submission claims no
mathematical or formalization authorship).**

- Informal solution: **ChatGPT 5.6 Pro, Samuel Korsky** (credited in the
  pinned source header of `Erdos119.lean`).
- Statement: **Formal Conjectures authors** (statement originates from the
  google-deepmind/formal-conjectures formalization of Erdős problem 119).
- Formalization: **Codex, Boris Alexeev** (credited in the pinned source
  header).
- Public port: [plby/lean-proofs](https://github.com/plby/lean-proofs) at
  commit `1268917deaaaa0d674f651287027baa26cea9920`, file
  `src/latest/ErdosProblems/Erdos119.lean` — a single-file closure over mathlib
  (`import Mathlib` only, 1788 lines).

**Verification summary.** The pinned file was extracted byte-exactly from the
pinned commit and compiled with the *current release* toolchain — Lean v4.34.0,
mathlib v4.34.0 (commit `5ed2965256430c3649e86755f9576b54eca72435`), direct
`lean.exe` invocation (no lake environment), mathlib built from source (no
prebuilt artifacts). Two documented porting patches were required by the
mathlib 4.33 → 4.34 API drift (see `verification/PORTING-DIFF-127.md`;
byte-level pinned-vs-verified diff between `verification/hashes-pinned-src.tsv`
and `verification/hashes-final.tsv`): `Finset.prod_le_prod` →
`Finset.prod_le_prod₀` (mathlib 4.34 renamed the two-hypothesis ordered-ring
form), and removal of an obsolete `rw [hsub]` whose pattern is normalized away
by 4.34's `norm_num`. With these, both the entry module
(`ErdosProblems.Erdos119`) and the audit module (`Audit127.lean`) compile with
exit 0 (driver run 2026-09-19 03:26:24 → 03:26:50; details in
`verification/current-release-v4.34.log`, which records the full two-pass
history including the first-pass porting error and one externally terminated
recompile that wrote no output). Dependency resolution via `lean --deps` exits
0 (closure: `Init` + `Mathlib` for the entry; `Init` + `ErdosProblems.Erdos119`
for the audit module). All sources, logs, and produced `.olean` files are
hash-pinned in `verification/hashes-final.tsv`.

**Axiom audit.** `#print axioms` on the four exported declarations
(`Erdos119.erdos_119`, `.parts.i`, `.parts.ii`, `.parts.iii_quantitative`)
yields exactly `[propext, Classical.choice, Quot.sound]` — the standard Lean
core axioms. No additional axioms, no `sorry`, no `unsafe` definitions.

## 中文

**问题（Erdős 问题表第 119 题，历史赏金 100 美元）**：若多项式 $p_n$ 的所有零点
都在单位圆上（$|z_i| = 1$），则 $p_n$ 在指定区域（单位圆）上的最大模
$M_n = \max_{|z|=1}|p_n(z)|$ 随次数 $n$ 的增长速度如何？被验证的形式化定理
（对单位圆上的任意零点序列）给出了回答：

- `Erdos119.erdos_119` — 存在绝对常数 $c > 0$（证明中 $c = 1/256$），使得对
  充分大的 $n$ 有 $\sum_{k<n} M_k > n^{1+c}$；
- `parts.iii_quantitative` — 对充分大的 $n$ 有 $C \cdot n^{5/4}/\sqrt{\log n}
  < \sum_{k<n} M_k$（某常数 $C > 0$）；
- `parts.ii` — 对无穷多个 $n$ 有 $M_n > n^c$；
- `parts.i` — $\limsup_n M_n = \infty$。

**形式化陈述（Lean 4，文件 `ErdosProblems/Erdos119.lean`，模块
`ErdosProblems.Erdos119`，命名空间 `Erdos119`）**：定理 `Erdos119.erdos_119`
及其三个推论，如上代码块所示。

**来源与署名（仅为署名，本提交不主张任何数学或形式化作者身份）**：非正式解答
出自 ChatGPT 5.6 Pro 与 Samuel Korsky；陈述出自 Formal Conjectures 作者
（源于 google-deepmind/formal-conjectures 对 Erdős 问题 119 的形式化）；
形式化出自 Codex 与 Boris Alexeev（以上均见 pinned 源码头注释）。公开移植版
位于 [plby/lean-proofs](https://github.com/plby/lean-proofs) 提交
`1268917deaaaa0d674f651287027baa26cea9920`（单文件闭包，仅 `import Mathlib`，
共 1788 行）。

**验证结论**：固定源按字节精确提取，并在当今发布版工具链（Lean v4.34.0 +
mathlib v4.34.0，mathlib 提交 `5ed2965…`，直接 `lean.exe` 调用，mathlib 从源码
构建、不使用预构建产物）上编译。因 mathlib 4.33→4.34 API 漂移需两处文档化
移植补丁（见 `verification/PORTING-DIFF-127.md` 及
`verification/hashes-pinned-src.tsv` 与 `verification/hashes-final.tsv` 的
逐字节差异）：`Finset.prod_le_prod` → `Finset.prod_le_prod₀`（mathlib 4.34
将双假设有序环形式改名），以及删除一条被 4.34 `norm_num` 规范化掉、不再匹配
的 `rw [hsub]`。补丁后入口模块与审计模块（`Audit127.lean`）编译均退出码 0
（驱动运行 2026-09-19 03:26:24 → 03:26:50；完整两轮历史、首轮移植错误及一次
被外部终止且未产生输出的重编译均如实记录于
`verification/current-release-v4.34.log`）。依赖解析（`lean --deps`）退出码
0（入口闭包：`Init` + `Mathlib`；审计模块：`Init` + `ErdosProblems.Erdos119`）。
全部源码、日志与产物 `.olean` 均以 SHA-256 固定于
`verification/hashes-final.tsv`。

**公理审计**：对四个导出声明（`Erdos119.erdos_119`、`parts.i`、`parts.ii`、
`parts.iii_quantitative`）执行 `#print axioms`，仅得
`[propext, Classical.choice, Quot.sound]` —— 即 Lean 核心公理集合；无额外
公理、无 `sorry`、无 `unsafe` 定义。
