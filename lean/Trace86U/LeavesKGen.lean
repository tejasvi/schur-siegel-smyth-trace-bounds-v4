import Trace86U.CheckSound10

/-! Composition of tiling checks of consecutive pieces of the leaf list (for the K groups). -/

namespace Trace86.UCert

open T86UCore

set_option maxRecDepth 200000 in
theorem leaves_length_K : leaves.length = 14337 := by decide +kernel

theorem take_append_drop_K (l : List Leaf) (a n : ℕ) : (l.drop a).take n ++ l.drop (a + n) = l.drop a := by
  have h := List.take_append_drop n (l.drop a)
  rwa [List.drop_drop] at h

theorem chunk_step_K {c : Ctx} {X kx Y ky XT kT a n : ℕ}
    (h1 : leavesOK c X kx ((leaves.drop a).take n) Y ky = true)
    (h2 : leavesOK c Y ky (leaves.drop (a + n)) XT kT = true) :
    leavesOK c X kx (leaves.drop a) XT kT = true := by
  have h := leavesOK_append c _ _ X kx Y ky XT kT h1 h2
  rwa [take_append_drop_K] at h

theorem take_step {c : Ctx} {X kx Y ky Z kz a n m t b : ℕ} (ht : n + m = t) (hb : a + n = b)
    (h1 : leavesOK c X kx ((leaves.drop a).take n) Y ky = true)
    (h2 : leavesOK c Y ky ((leaves.drop b).take m) Z kz = true) :
    leavesOK c X kx ((leaves.drop a).take t) Z kz = true := by
  subst ht hb
  rw [List.take_add, List.drop_drop]
  exact leavesOK_append c _ _ X kx Y ky Z kz h1 h2

end Trace86.UCert
