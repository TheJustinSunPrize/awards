import Lake
open System Lake DSL

package jsp070_verify where
  -- 独立最小验证工程：仅编译 Erdos42.lean（standalone flat bundle，仅依赖 Mathlib）

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib Erdos42
