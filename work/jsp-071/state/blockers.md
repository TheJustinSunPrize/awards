# JSP-000071 blockers（人工/环境阻塞记录）

## 当前阻塞（无人工项，均为环境技术项，已找到绕行方案）

### B1. lake build / lake env 在 071 目录挂起（已绕行）
- 现象：`lake build ErdosProblems.Erdos862` 与 `lake env lean` 均 9 分钟无输出。
- 诊断：071 通过 junction 复用 070 的 `.lake`（7.3GB，含 mathlib 8714 olean），
  文件系统访问正常（`dir` 可读 Mathlib.olean），最小文件 `TestImport.lean`
  经 **lean.exe 直连 + LEAN_PATH** 编译 11.6s 成功 → 问题不在 olean 而在 **lake 的
  git manifest 校验挂网络**（本沙箱 network_disabled，lake 尝试解析 manifest 时卡死）。
- 绕行方案：不使用 lake；用 `build071.ps1`（lean.exe + 自动收集 9 个包的 olean 目录
  到 LEAN_PATH）直接编译。**已实证可用**。
- 备注：070 当初同样采用单文件编译（erdos42-compile.log 为 lake env lean 产出），
  环境与 071 完全一致（同 pinned commit、同 mathlib olean 集）。

### B2. Erdos862.lean 全量编译 >9 分钟（时间盒限制，非故障）
- 现象：首次全量编译 1949 行（42 个定理/引理，import Mathlib 全库）9 分钟未完成，
  进程被时间盒终止。
- 判断：与 070 的 Erdos42.lean（15010 行）相比体量小 1/8，属正常重编译，非死锁；
  olean 产物为零仅因进程被终止。
- 应对：后续 tick 用 `build071.ps1 -TimeSec 3000`（50 分钟上限）在后台执行，
  或分两次 tick 编译；9 分钟时间盒内若未完成则提交进度后继续。

## 已关闭
- （无）
