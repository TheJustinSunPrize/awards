import Statement
import ErdosProblems.Erdos166

namespace JSP000163

set_option autoImplicit false

/-- The pinned Erdos166 development proves the frozen JSP-000163 statement. -/
theorem proof : targetStatement := by
  exact Erdos166.erdos_166

end JSP000163
