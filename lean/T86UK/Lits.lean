import T86UCore.Lits
import T86UCore.Leaves

/-! The literal context equals the computed one (K). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace T86UCore.T86UK

theorem ctx_eq : mkCtx = ctxULit := by decide +kernel

end T86UCore.T86UK
