import AuxCommon.LogKSound
import Trace86.PolySound
import Trace86.AnaSound
import Trace86.TailSound
import Trace86.Assembly
import Trace86.HatGen

/-!
# Soundness of the 86a checker, part 1: logarithm tables and node records (adapted from the companion Mahler-measure formalization)

* `tab_ok`, `l2_ok`, `logT_sound`: the logarithm `logT TAB L2` of the checker encloses `2^P log(a/b)`.
* `recOf`, `mkRecs_eq`, `recNum_div`: the node records of the checker are `(n_i, sign C_i, ⌊2^QS C_i⌋, ⌈2^QS C_i⌉)`
  with `C_i = slopeJump NN eR GR i`; here the `C_i` come from the hat weights (`hatC`): `C_i = L_{i+1} + M_i + R_{i-1}`.
-/

open Polynomial

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

/-! ## Tables -/

theorem tab_check : tableCheck 64 24 48 TAB 66 = true := by decide +kernel

theorem l2_check : l2Check 64 24 48 L2.1 L2.2 = true := by decide +kernel

theorem tab_ok : TableOK P TAB WT := tableCheck_sound tab_check

theorem l2_ok : ((L2.1 : ℕ) : ℝ) ≤ 2 ^ P * Real.log 2 ∧ 2 ^ P * Real.log 2 ≤ ((L2.2 : ℕ) : ℝ) :=
  l2Check_sound l2_check

/-- **The checker's logarithm is sound.** -/
theorem logT_sound {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((logT TAB L2 a b).1 : ℝ) ≤ 2 ^ P * Real.log ((a : ℝ) / b) ∧
      2 ^ P * Real.log ((a : ℝ) / b) ≤ ((logT TAB L2 a b).2 : ℝ) := by
  unfold logT
  refine logK_sound ha hb tab_ok ?_ ?_
  · have := l2_ok.1; simpa using this
  · have := l2_ok.2; simpa using this

/-! ## Node records -/

/-- `C_i` as a fraction: the checker's `hatC` entry `L_{i+1} + M_i + R_{i-1}`. -/
def recC (i : ℕ) : ℤ × ℕ :=
  qadd (qadd (hatAt hatL RS nodes rho (i + 1)) (hatAt hatM RS nodes rho i)) (hatAt hatR RS nodes rho (i - 1))

/-- Numerator and denominator of `C_i` (irreducible: unfolding them would evaluate the data lists). -/
@[irreducible] def recNum (i : ℕ) : ℤ := (recC i).1
@[irreducible] def recDen (i : ℕ) : ℕ := (recC i).2

/-- The intended record of node `i`. -/
def recOf (i : ℕ) : NRec :=
  ⟨nodes.getD i 0, Int.sign (recNum i), fdiv (recNum i * 2 ^ QS) (recDen i), cdiv (recNum i * 2 ^ QS) (recDen i)⟩

theorem nodes_length' : nodes.length = rho.length + 2 := by
  have h1 := nodes_length
  have h2 := rho_length
  omega

theorem mkRecs_eq : mkRecs = (List.range (NN + 1)).map recOf := by
  have hc : (hatC RS nodes rho).length = NN + 1 := by
    rw [hatC_length nodes_length']
    have := rho_length
    omega
  apply List.ext_getElem
  · simp only [mkRecs, mkRecsQ, List.length_zipWith, hc, nodes_length, List.length_map, List.length_range, min_self]
  · intro i h1 h2
    have hi : i < NN + 1 := by rw [List.length_map, List.length_range] at h2; exact h2
    have hin : i < nodes.length := by rw [nodes_length]; exact hi
    rw [List.getElem_map, List.getElem_range]
    unfold recOf recNum recDen recC
    simp only [mkRecs, mkRecsQ, List.getElem_zipWith, hatC_getElem nodes_length', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hin, Option.getD_some]

/-- The value of a fraction. -/
noncomputable def qv (x : ℤ × ℕ) : ℝ := (x.1 : ℝ) / x.2

theorem qv_qadd {x y : ℤ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (qadd x y).2 ∧ qv (qadd x y) = qv x + qv y := by
  refine ⟨Nat.mul_pos hx hy, ?_⟩
  have hx' : (0 : ℝ) < x.2 := by exact_mod_cast hx
  have hy' : (0 : ℝ) < y.2 := by exact_mod_cast hy
  simp only [qv, qadd]
  push_cast
  field_simp

theorem DEC_real : (DEC : ℝ) = 10 ^ 12 := by norm_num [DEC]

theorem gapL_facts {j : ℕ} (h0 : 0 < j) (hj : j ≤ NN) :
    0 < gapL nodes j ∧ (gapL nodes j : ℝ) = (eR j - eR (j - 1)) * 10 ^ 12 := by
  have h := nodes_inc (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at h
  refine ⟨by unfold gapL; omega, ?_⟩
  unfold gapL eR
  rw [Nat.cast_sub h.le]
  ring

theorem rho_len_NN : rho.length + 1 = NN := rho_length

/-- The hat contributions as reals (zero when there is no hat at node `j`). -/
theorem hatAt_facts (j : ℕ) :
    (0 < (hatAt hatL RS nodes rho j).2 ∧ qv (hatAt hatL RS nodes rho j) = GR j / (eR j - eR (j - 1))) ∧
    (0 < (hatAt hatM RS nodes rho j).2 ∧
      qv (hatAt hatM RS nodes rho j) = -(GR j / (eR (j + 1) - eR j)) - GR j / (eR j - eR (j - 1))) ∧
    (0 < (hatAt hatR RS nodes rho j).2 ∧ qv (hatAt hatR RS nodes rho j) = GR j / (eR (j + 1) - eR j)) := by
  unfold hatAt
  rw [rho_len_NN]
  by_cases hc : 0 < j ∧ j < NN
  · simp only [if_pos hc]
    obtain ⟨ha0, ha⟩ := gapL_facts hc.1 hc.2.le
    obtain ⟨hb0, hb⟩ := gapL_facts (j := j + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hb
    have hA : 0 < eR j - eR (j - 1) := by
      have := eR_lt (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      linarith
    have hB : 0 < eR (j + 1) - eR j := by have := eR_lt j hc.2; linarith
    have hG : GR j = 2 * rhoR j / ((eR (j + 1) - eR j) + (eR j - eR (j - 1))) := by
      unfold GR
      rw [if_pos hc]
      ring_nf
    have hr : rhoR j = (rho.getD (j - 1) 0 : ℝ) / 2 ^ RS := rfl
    have h2 : (0 : ℝ) < 2 ^ RS := by positivity
    have ha' : (0 : ℝ) < gapL nodes j := by exact_mod_cast ha0
    have hb' : (0 : ℝ) < gapL nodes (j + 1) := by exact_mod_cast hb0
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [hatL]; positivity
    · simp only [qv, hatL]
      push_cast
      rw [hG, hr, ha, hb, DEC_real]
      field_simp
      ring
    · simp only [hatM]; positivity
    · simp only [qv, hatM]
      push_cast
      rw [hG, hr, ha, hb, DEC_real]
      field_simp
      ring
    · simp only [hatR]; positivity
    · simp only [qv, hatR]
      push_cast
      rw [hG, hr, ha, hb, DEC_real]
      field_simp
      ring
  · simp only [if_neg hc]
    have hG : GR j = 0 := by unfold GR; rw [if_neg hc]
    simp [qv, hG]

theorem GR_gt {k : ℕ} (hk : NN ≤ k) : GR k = 0 := by
  unfold GR
  rw [if_neg (by omega)]

theorem recDen_pos {i : ℕ} (_hi : i ≤ NN) : 0 < recDen i := by
  obtain ⟨⟨hL, -⟩, -, -⟩ := hatAt_facts (i + 1)
  obtain ⟨-, ⟨hM, -⟩, -⟩ := hatAt_facts i
  obtain ⟨-, -, ⟨hR, -⟩⟩ := hatAt_facts (i - 1)
  unfold recDen recC
  exact (qv_qadd (qv_qadd hL hM).1 hR).1

theorem recNum_div {i : ℕ} (hi : i ≤ NN) : (recNum i : ℝ) / (recDen i : ℝ) = CR i := by
  obtain ⟨⟨hL, vL⟩, -, -⟩ := hatAt_facts (i + 1)
  obtain ⟨-, ⟨hM, vM⟩, -⟩ := hatAt_facts i
  obtain ⟨-, -, ⟨hR, vR⟩⟩ := hatAt_facts (i - 1)
  have h1 := qv_qadd hL hM
  have h2 := qv_qadd h1.1 hR
  have hv : (recNum i : ℝ) / (recDen i : ℝ) = qv (recC i) := by unfold recNum recDen qv; rfl
  rw [hv]
  unfold recC
  rw [h2.2, h1.2, vL, vM, vR]
  have hNN : 0 < NN := by decide
  unfold CR slopeJump slope
  rw [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [if_pos hNN, if_neg (by omega), GR_zero]
    simp
  · rw [show i - 1 + 1 = i by omega]
    by_cases hiN : i < NN
    · rw [if_pos hiN, if_pos ⟨hi0, hi⟩]
      ring
    · have hiN' : i = NN := by omega
      subst hiN'
      rw [if_neg hiN, if_pos ⟨hi0, hi⟩, GR_gt (Nat.le_succ NN), GR_NN]
      ring

/-- The record of node `i` encloses `2^QS C_i`, and its sign field is the sign of `C_i`. -/
theorem recOf_spec {i : ℕ} (hi : i ≤ NN) :
    ((recOf i).clo : ℝ) ≤ 2 ^ QS * CR i ∧ 2 ^ QS * CR i ≤ ((recOf i).chi : ℝ) ∧
      ((recOf i).sg = 0 ↔ CR i = 0) ∧ (0 < (recOf i).sg ↔ 0 < CR i) ∧ (recOf i).n = nodes.getD i 0 := by
  have hd := recDen_pos hi
  have hdR : (0 : ℝ) < recDen i := by exact_mod_cast hd
  have hC := recNum_div hi
  have hQ : (0 : ℝ) < 2 ^ QS := by positivity
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · have := fdiv_le (recNum i * 2 ^ QS) hd
    show ((fdiv (recNum i * 2 ^ QS) (recDen i) : ℤ) : ℝ) ≤ _
    rw [← hC]
    push_cast at this
    calc _ ≤ ((recNum i : ℝ) * 2 ^ QS) / recDen i := this
      _ = 2 ^ QS * ((recNum i : ℝ) / recDen i) := by ring
  · have := le_cdiv (recNum i * 2 ^ QS) hd
    show _ ≤ ((cdiv (recNum i * 2 ^ QS) (recDen i) : ℤ) : ℝ)
    rw [← hC]
    push_cast at this
    calc 2 ^ QS * ((recNum i : ℝ) / recDen i) = ((recNum i : ℝ) * 2 ^ QS) / recDen i := by ring
      _ ≤ _ := this
  · show Int.sign (recNum i) = 0 ↔ CR i = 0
    rw [Int.sign_eq_zero_iff_zero, ← hC]
    constructor
    · intro h; rw [h]; simp
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact_mod_cast h
      · exact absurd h hdR.ne'
  · show 0 < Int.sign (recNum i) ↔ 0 < CR i
    rw [Int.sign_pos_iff, ← hC]
    constructor
    · intro h; exact div_pos (by exact_mod_cast h) hdR
    · intro h
      have := (div_pos_iff_of_pos_right hdR).mp h
      exact_mod_cast this

end Trace86.Cert
