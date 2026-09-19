import Lake
open System Lake DSL

package jsp070_verify_current where
  -- Independent re-verification on the current mathlib release (v4.34.0)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib Jsp616
