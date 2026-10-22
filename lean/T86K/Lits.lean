import T86Core.Lits
import T86Core.Leaves

/-! The literal context equals the computed one (K). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace T86Core.T86K

theorem ctx_eq : mkCtx iLoNum 128 = ctxLit := by decide +kernel

end T86Core.T86K
