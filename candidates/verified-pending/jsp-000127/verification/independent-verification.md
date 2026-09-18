# 独立验证说明 — Independent verification — JSP-000127

Erdős 问题 119（JSP-000127）：若多项式所有零点都在单位圆上，其最大模在指定
区域（单位圆）上随次数增长的速度如何？
(Erdős problem 119 (JSP-000127): how does the maximum modulus on the unit circle
of a polynomial whose zeros all lie on the unit circle grow with its degree?)

## 1. 验证范围（Scope）

验证对象为 plby/lean-proofs @ `1268917deaaaa0d674f651287027baa26cea9920` 的
`src/latest/ErdosProblems/Erdos119.lean`（1788 行，单文件闭包，仅
`import Mathlib`）。导出的四个声明：

- `Erdos119.erdos_119`：对任意零点在单位圆上的序列 z，存在绝对常数 c > 0
  （c = 1/256），最终有 ∑_{k<n} M z k > n^(1+c)；
- `Erdos119.erdos_119.parts.iii_quantitative`：最终
  C · n^(5/4)/√(log n) < ∑_{k<n} M z k（某 C > 0）；
- `Erdos119.erdos_119.parts.ii`：{n | M z n > n^c} 为无限集（某 c > 0）；
- `Erdos119.erdos_119.parts.i`：limsup_n (M z n) = ∞。

其中 M z n = sSup {‖p z n w‖ | ‖w‖ = 1}，p z n = ∏_{i<n} (w - z i)。

Scope: the pinned single-file closure `Erdos119.lean` and its four exported
declarations listed above.

## 2. 工具链与环境（Toolchain and environment）

- Lean v4.34.0（`I:\Lean4\.elan\toolchains\leanprover--lean4---v4.34.0\bin\lean.exe`），
  直接调用 lean.exe，不使用 lake 环境；
- mathlib v4.34.0 @ `5ed2965256430c3649e86755f9576b54eca72435`，本地源码构建
  （MATHLIB_CACHE_DISABLE=1），不使用任何预构建产物；
- Windows 11 x86_64，非特权用户会话，编译期间网络禁用；
- LEAN_PATH = 本地 `.lake\build\lib\lean` + 本地 `olean` + jsp-071 全部
  `.lake\packages\*\ .lake\build\lib\lean`（10 项）。

## 3. 验证过程（Verification process）

1. **固定源提取**：`git cat-file blob` 按字节精确提取 pinned 文件
   （70757 字节，SHA-256 `09f0888e…`，见 hashes-pinned-src.tsv）。
2. **移植补丁**：mathlib 4.33→4.34 API 漂移需要 2 处文档化修改
   （PORTING-DIFF-127.md）——`Finset.prod_le_prod` → `Finset.prod_le_prod₀`
   （第 58 行）；删除 `cube_le_six_choose` 中失效的 `have hsub`+`rw [hsub]`
   （第 776-777 行）。两处均为最小改动，逐条单独验证。
3. **编译闭环**（驱动脚本 compile127.ps1，串行）：
   - 03:22:54 首轮：Erdos119 在第 777 行报错（rewrite 模式 `m + 3 - 2` 在
     4.34 中已不存在）→ 应用补丁 2；
   - 03:26:24 最终轮：Erdos119 exit=0（17 s）→ Audit127 exit=0（9 s）→
     ALL DONE 03:26:50；
   - 日志按字节忠实重录（03:32-03:34，cmd 重定向）：03:32:14 一次重编译被
     外部进程终止（exit=-1，未产生输出），03:33:54 重试 exit=0 且 .olean
     与驱动产物字节一致（SHA-256 相同）。
4. **依赖解析**：`lean --deps` 两模块均 exit=0（Erdos119：Init + Mathlib；
   Audit127：Init + ErdosProblems.Erdos119）。
5. **零 sorry 扫描**：对 1788 行源码 findstr，`sorry`/`admit` 出现次数为 0。
6. **公理审计**：`#print axioms` 四个声明均恰为
   `[propext, Classical.choice, Quot.sound]`；无 sorryAx、无用户公理、无
   unsafe。（首轮输出中的 sorryAx 是第 777 行错误触发的 Lean 恢复桩，补丁后
   消失。）

## 4. 产物与哈希（Artifacts and hashes）

- hashes-pinned-src.tsv：pinned 原始字节（1 个文件）。
- hashes-final.tsv：验证用源（补丁后）、Audit127.lean、PORTING-DIFF-127.md、
  两个 .olean、两个编译日志、current-release-v4.34.log（共 8 项，SHA-256 +
  字节数）。
- current-release-v4.34.log：策划式构建日志，内嵌最终原始驱动输出与两个
  步骤日志全文，如实记录两轮历史与外部终止事件。

## 5. 复现步骤（Reproduction steps）

```
git -C <lean-proofs-clone> cat-file blob 1268917de…:src/latest/ErdosProblems/Erdos119.lean > pinned\Erdos119.lean
# 应用 PORTING-DIFF-127.md 的两处补丁
copy pinned\Erdos119.lean verify-current\ErdosProblems\Erdos119.lean
# LEAN_PATH 见第 2 节；在 verify-current 下：
lean.exe ErdosProblems\Erdos119.lean -o .lake\build\lib\lean\ErdosProblems\Erdos119.olean
lean.exe Audit127.lean -o .lake\build\lib\lean\Audit127.olean
```

## 6. 与问题陈述的一致性（Statement match）

`Erdos119.erdos_119`（及其 parts）与 STMT-jsp-000127-v1 一致：对所有零点在
单位圆上的序列，最大模部分和最终超过 n^(1+c)（c=1/256），量化版本给出
C·n^(5/4)/√(log n) 的下界，推论为无穷多个 n 满足 M_n > n^c 且
limsup M_n = ∞。这直接回答了问题所问的增长速度。

## 7. 沙箱与可信性声明（Sandbox attestation）

- 网络禁用；mathlib 源码构建、无预构建产物；非特权用户；
- 不使用任何额外公理、sorry、unsafe；仅依赖 Lean 核心公理；
- 编译期间唯一的外部事件：03:32:14 一次 Erdos119 重编译被宿主级外部进程
  终止（未产生输出，重试后 exit=0 且产物字节一致）；驱动最终轮（03:26:24
  → 03:26:50）全程无干扰。

## 8. 相关记录（Related records）

- `record.yaml`：record 与 build_log（SHA-256 `bf6ac22c…`，5061 字节）；
- `statement.yaml`：STMT-jsp-000127-v1；
- `PORTING-DIFF-127.md`：两处移植补丁；
- `hashes-pinned-src.tsv` / `hashes-final.tsv`：逐字节差异。
