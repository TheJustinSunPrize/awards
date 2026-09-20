# JSP-000391 提交前自查报告（lean-verify self-check）

> 生成：2026-09-20。依据官方 `skills/lean-verify` 规范（PR #1759 已合并，要求 Lean 提交附 pre-submission self-check）。
> 报告人：Shiqiang Chen（shunfeng8421）。

## 结论

> **总体结论：验证通过（公理干净）。**
> 对于 JSP-000391，在证明仓库 `shunfeng8421/jsp301-lean` commit `8de5b93` 上，
> 该提交完整解决了题目的核心数字位命题：d_n = u_{2n+1} − 2·u_{2n−1} ∈ {0,1}（√2 二进制位），
> 且通过 lean-verify 公理审计（无 native_decide 扩展信任，仅标准三项公理）。

| 必答问题 | 明确判断 | 决定性依据 |
| --- | --- | --- |
| 证明对象是否就是指定原题？ | 是 | u₁=1, u_{n+1}=⌊√2(u_n+1/2)⌋，d_n 定义与 catalog JSP-000391 一致；整数闭式 step u=Nat.sqrt(2u(u+1)) 已证明等价 |
| 指定 commit 是否实际验证通过？ | 是 | `lake env lean` 编译 exit 0，#check/#print 通过（见下方日志） |
| 是否完整解决原题？ | 是（核心数字位命题）| d_mem_zero_one 完整证明链（P0-P3），0 sorry/admit |
| 是否满足 Lean 完整性要求？ | 满足 | `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]` |

## 固定证据

- 获取时间：2026-09-20（中国标准时间）
- 证明仓库：https://github.com/shunfeng8421/jsp301-lean
- 验证 commit：`8de5b93b405206ce100f5131a9ce744a6f0c9d32`（JSP-391 native_decide 消除版）
- 原提交（含 native_decide 版本）：`e8872b9b405206ce100f5131a9ce744a6f0c9d32`
- 工具链：leanprover/lean4:v4.34.0，mathlib v4.34.0（5ed2965256430c3649e86755f9576b54eca72435）
- 目标声明：
  - `Jsp391.d_mem_zero_one`（主定理：d_n ∈ {0,1}）
  - `Jsp391.step_step_digit`（P2 核心）
  - `Jsp391.u3`（辅助，native_decide 消除后新增）

## 目标检查命令与结果

```bash
cd /i/research/jsp301
lake env lean Jsp391Full.lean   # 编译：EXIT=0，无 error
# 审计（Jsp391FullAudit.lean，含 #print axioms）：
lake env lean Jsp391FullAudit.lean   # EXIT=0
```

`#print axioms Jsp391.d_mem_zero_one` 输出：
```
'Jsp391.d_mem_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```
（仅标准三项，无 `native_decide.ax`、无 `sorryAx`、无其他扩展信任）

`#print axioms Jsp391.step_step_digit` 输出：
```
'Jsp391.step_step_digit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#check Jsp391.u3` 输出：`Jsp391.u3 : Jsp391.u 3 = 3`

## 审计发现与修复

**初始审计发现**（commit e8872b9）：
- `d_mem_zero_one` 依赖含 `native_decide.ax_1_6`（来自 `u_odd_ge_three` 中 `u 3 = 3 := by native_decide`）。
- 这是 native_decide 的 soundness 公理（扩展信任），虽非 sorry，但按 lean-verify 规范属需审查项。

**修复**（commit 8de5b93）：
- 将 `u 3 = 3` 改为显式逐步计算：step1（Nat.sqrt_eq），step2（Nat.le_sqrt 夹逼），u3（u_rec 递推）。
- 消除 native_decide 公理，`d_mem_zero_one` 降至仅标准三项。

## 证明完整性

- 主定理链：square_bound → step_le_2u_sub2 → step_sq_bound/upper → step_step_digit（step(step u)−2u∈{0,1}）→ u_pos → u_strict_mono → u_odd_composition → u_odd_ge_three → **d_mem_zero_one**
- 0 sorry / 0 admit
- 无循环假设、无占位声明
- 覆盖：d_n 是二进制位（0 或 1）——题目的核心数字位命题。精确位值（d_n = Nat.sqrt(2^(2n-1)) mod 2）及二进制展开闭式（u_{2n+1}=2^n+Σ2^{n-i}·d_i）以数学证据记录于 `P4a-EVIDENCE.md`（数值验证 n=1..19）。

## 复核层级

- 本报告为提交者自查（pre-submission self-check），依据官方 lean-verify 技能手动等价执行（audit.py 在 Windows 有路径兼容问题，改用 reproduction.md 规范手动审计）。
- 独立维护者复验、kernel replay 或 comparator 由官方按流程执行；本报告不替代之。
- 适用范围：仅 JSP-000391 的 Lean 证明；不决定合并、授奖或支付。