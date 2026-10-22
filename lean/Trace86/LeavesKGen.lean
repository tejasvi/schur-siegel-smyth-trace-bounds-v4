import Trace86.CheckSoundE5

/-! The length of the leaf list (for the K groups; the composition lemmas are in `Trace86.CheckSoundE5`). -/

namespace Trace86.Cert

open T86Core

set_option maxRecDepth 200000 in
theorem leaves_length_K : leaves.length = 14956 := by decide +kernel

end Trace86.Cert
