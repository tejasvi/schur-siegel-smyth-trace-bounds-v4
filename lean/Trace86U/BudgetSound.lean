import Trace86U.CheckSound9

/-!
# Condition (S) of the 86a upper bound: `∑ b_j deg Q_j < 1`
-/

open Polynomial

namespace Trace86.UCert

open T86UCore

/-- `ℕ`-power with the instance of core Lean (as elaborated in `T86UCore`). -/
local notation:75 a:76 " ^ᶜ " b:75 => @HPow.hPow ℕ ℕ ℕ (@instHPow ℕ ℕ (@instPowNat ℕ instNatPowNat)) a b

theorem cast_powC' (a b : ℕ) : ((a ^ᶜ b : ℕ) : ℝ) = (a : ℝ) ^ b := Nat.cast_pow a b

set_option maxRecDepth 20000 in
theorem cwSh_max : cwSh.foldl max 0 = 44 := by decide +kernel

set_option maxRecDepth 20000 in
theorem cwSh_le : ∀ j < 21, cwSh.getD j 0 ≤ 44 := by decide +kernel

/-- The left side of the budget check (common denominator `2^S`). -/
def lhsB : ℕ :=
  (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ᶜ (cwSh.foldl max 0 - x.2.2)) 0

theorem budgetOK_iff : budgetOK = true ↔ lhsB < 2 ^ᶜ (cwSh.foldl max 0) := by
  simp only [budgetOK, lhsB, decide_eq_true_eq]

theorem lhsB_gen (S : ℕ) :
    (List.zip polys (List.zip cwNum cwSh)).foldl
      (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ᶜ (S - x.2.2)) 0 =
    ∑ j ∈ Finset.range 21, cwNum.getD j 0 * ((polys.getD j []).length - 1) * 2 ^ᶜ (S - cwSh.getD j 0) := by
  have hsum : ∀ (g : ℕ → ℕ), ((List.range 21).map g).sum = ∑ j ∈ Finset.range 21, g j :=
    fun g => list_sum_range g 21
  rw [polyZip_eq, foldl_add_eq_sum, zero_add, List.map_map, hsum]
  rfl

/-- **(S)**: `∑ b_j deg Q_j < 1`. -/
theorem budget_sound (h : budgetOK = true) :
    ∑ j ∈ Finset.range 21, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) < 1 := by
  rw [budgetOK_iff] at h
  have hle : ∀ j < 21, cwSh.getD j 0 ≤ cwSh.foldl max 0 := by
    rw [cwSh_max]
    exact cwSh_le
  have hL : lhsB = ∑ j ∈ Finset.range 21,
      cwNum.getD j 0 * ((polys.getD j []).length - 1) * 2 ^ᶜ (cwSh.foldl max 0 - cwSh.getD j 0) :=
    lhsB_gen _
  rw [hL] at h
  generalize cwSh.foldl max 0 = S at hle h
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  have hR : ((∑ j ∈ Finset.range 21,
      cwNum.getD j 0 * ((polys.getD j []).length - 1) * 2 ^ᶜ (S - cwSh.getD j 0) : ℕ) : ℝ) < ((2 ^ᶜ S : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast [cast_powC'] at hR
  have e : ∑ j ∈ Finset.range 21, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) =
      (∑ j ∈ Finset.range 21, (cwNum.getD j 0 : ℝ) * (((polys.getD j []).length - 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (S - cwSh.getD j 0)) / 2 ^ S := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := hle j (Finset.mem_range.mp hj)
    unfold cj
    rw [pow_sub₀ (2 : ℝ) two_ne_zero hj']
    field_simp
  rw [e, div_lt_one hS]
  convert hR using 2

end Trace86.UCert
