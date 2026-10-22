import T86K.ELits

/-! The literal energy data equal the computed ones (K). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace T86Core.T86K

theorem tabI_eq : TABI = tabILit := by decide +kernel

theorem l2I_eq : L2I = l2ILit := by decide +kernel

theorem recsI_eq : recsI = recsILit := by decide +kernel

end T86Core.T86K
