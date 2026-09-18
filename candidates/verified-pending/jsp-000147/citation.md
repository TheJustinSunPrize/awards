# Citation — JSP-000147

## English

**Problem.** Erdős problems list, problem 146 — "How many edges can a graph have
while excluding a given bipartite graph of bounded degeneracy?"
(https://www.erdosproblems.com/146, historical bounty $500).

The Erdős–Simonovits degeneracy conjecture predicts that every bipartite
$r$-degenerate graph $H$ satisfies $\operatorname{ex}(n,H) = O(n^{2-1/r})$.
The formalized theorem below is a *disproof* of that conjecture: it exhibits a
connected bipartite $2$-degenerate graph $H$ (a Hamming graph) and constants
$c, \varepsilon > 0$ such that $\operatorname{ex}(n,H) \ge c \cdot n^{3/2+\varepsilon}$
eventually, strictly above the conjectured $O(n^{3/2})$ bound.

**Formal statement (Lean 4, file `Erdos146.lean`).**

```lean
theorem not_erdos_146 :
    ¬ (∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
      0 < r → H.IsBipartite → IsDegenerate r H →
        Asymptotics.IsBigO Filter.atTop
          (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (((2 : ℕ) : ℝ) - 1 / (r : ℝ))))
```

**Authorship and provenance (credit only, no authorship claim).**

- Mathematical solution and first formalization: OpenAI "ten-proofs" project
  (Astra, OpenAI team), see the in-file comment in `Erdos146.lean`; the original
  development is `CompactnessAndDegeneracy.lean` in OpenAI ten-proofs @
  `a13547c6be4563746881d0b3b4c9fd03f72f0484` (bitbucket mirror).
- Public port: [plby/lean-proofs](https://github.com/plby/lean-proofs) @
  `1268917deaaaa0d674f651287027baa26cea9920`, files
  `src/latest/ErdosProblems/Erdos146.lean` and
  `src/latest/ErdosProblems/Erdos146/*.lean` (Apache-2.0, `LICENSE` shipped in
  the closure).
- This submission claims **no mathematical or formalization authorship**. It is
  an independent verification contribution (see `verification/record.yaml`).

**Verification summary.** All seven Lean files of the pinned closure were
compiled unmodified with the *current release* toolchain — Lean v4.34.0 with
mathlib v4.34.0 (mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`) —
using direct `lean.exe` invocations in import order, then the entry module and
an audit module were compiled against the produced `.olean`s. Every step exited
0 with no source edits, warnings only. The build log
(`verification/current-release-v4.34.log`) records all commands, exit codes and
elapsed times; both `.lean` files and the final `Erdos146.olean` are hash-pinned
in `verification/record.yaml`.

**Axiom audit.** `#print axioms` run on the two exported theorems yields exactly
`[propext, Classical.choice, Quot.sound]` — the standard Lean core axioms — as
attested in the upstream source header. In particular, the proof uses no
additional axioms or `unsafe` definitions.

## 中文

**问题（Erdős 问题表第 146 题，历史赏金 500 美元）**：给定一个二分图
$H$，若限制其退化度（degeneracy），则不含 $H$ 作为子图的 $n$ 顶点图至多能
有多少条边？Erdős–Simonovits 退化猜想断言：对每个二分 $r$-退化图 $H$，
$\operatorname{ex}(n,H) = O(n^{2-1/r})$。

**本形式化工作的内容**：被验证文件 `Erdos146.lean`（Lean 4）否定了该猜想
（定理 `Erdos146.not_erdos_146`），并构造出反例（定理
`Erdos146.twoDegenerateExtremalCounterexample`）：一个连通的二分 2-退化
Hamming 图 $H$，使得 $\operatorname{ex}(n,H) \ge c \cdot n^{3/2+\varepsilon}$
最终成立，严格超过推测的 $O(n^{3/2})$。

**来源**：数学解答与最初的形式化出自 OpenAI ten-proofs 项目（Astra, OpenAI），
原始文件 `CompactnessAndDegeneracy.lean`（提交
`a13547c6be4563746881d0b3b4c9fd03f72f0484`）；公开移植版位于
[plby/lean-proofs](https://github.com/plby/lean-proofs) 提交
`1268917deaaaa0d674f651287027baa26cea9920`（Apache-2.0）。本提交**不主张**
任何数学或形式化作者身份，仅为独立验证贡献。

**验证结论**：固定闭包的 7 个 Lean 文件在当今发布版工具链（Lean v4.34.0 +
mathlib v4.34.0，mathlib 提交 `5ed2965…`）上按导入顺序逐个用 `lean.exe`
直接编译，零源码修改、全部退出码 0；入口模块与审计模块亦通过。编译日志
（`verification/current-release-v4.34.log`）记录全部命令、退出码与耗时；
源码与产物 `.olean` 的哈希均固定在 `verification/record.yaml` 中。

**公理审计**：对两条导出定理执行 `#print axioms`，仅得
`[propext, Classical.choice, Quot.sound]` — 即 Lean 核心公理集合，无任何
额外公理或 `unsafe` 定义。