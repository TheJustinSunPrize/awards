import Lake
open Lake DSL

package jsp000078_scope_completion where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

lean_lib ErdosProblems
lean_lib FormalConjecturesForMathlib
@[default_target] lean_lib JSP000078
