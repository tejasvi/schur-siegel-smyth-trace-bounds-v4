import Trace86.CheckSoundE1
import Trace86.CheckSoundE2

/-!
# Soundness of the end-point form, part 3: the node part of a chord leaf from the end-point data

From the end-point data `A` at `p` and `B` at `q`: no node with `C_i ≠ 0` strictly inside `(p, q)`, upper bounds of
`2^P U(p)`, `2^P U(q)` without the singular terms, and the upper bound `m` of the node part of the curvature, as used by
the chord leaf theorem (`chordLBC_sound`).
-/

open Polynomial Set

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

/-- No node with `C_i ≠ 0` strictly inside `(p, q)` when the counts agree. -/
theorem nin_of_counts {Xp Xq k : ℕ} (hpq : Xp < Xq)
    (hcnt : (epAt (mkCtx iLoNum 128) Xq k).cl = (epAt (mkCtx iLoNum 128) Xp k).cle) :
    ∀ i ≤ NN, CR i ≠ 0 → ¬ ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) < eR i ∧ eR i < (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) := by
  set p : ℝ := (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)
  set q : ℝ := (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)
  have hpqR : p < q := div_lt_div_of_pos_right (by exact_mod_cast hpq) (DEC_pow_pos k)
  obtain ⟨-, -, -, -, hq5, -, -, -⟩ := epAt_spec Xq k
  obtain ⟨-, -, -, -, -, hp6, -, -⟩ := epAt_spec Xp k
  rw [hq5, hp6] at hcnt
  have hle : ∀ i ∈ Finset.range (NN + 1), cleT p i ≤ clT q i := by
    intro i _
    unfold cleT clT
    split_ifs with h1 h2 <;> try omega
    exact absurd ⟨h1.1, lt_of_le_of_lt h1.2 hpqR⟩ h2
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hcnt.symm
  intro i hi hC ⟨h1, h2⟩
  have := heq i (Finset.mem_range.mpr (by omega))
  unfold cleT clT at this
  rw [if_neg (fun h => absurd h.2 (not_le.mpr h1)), if_pos ⟨hC, h2⟩] at this
  omega

theorem singI_iff {k Xp Xq i : ℕ} :
    singI k Xp Xq i ↔ 0 < CR i ∧ (eR i = (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) ∨
      eR i = (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) := by
  unfold singI
  rw [eR_eq_pt_iff, eR_eq_pt_iff]

theorem Hk_zero : Hk 0 = 0 := by simp [Hk]

theorem Hk_neg (t : ℝ) : Hk (-t) = Hk t := by simp [Hk, abs_neg]

/-- `2^(P+QS) (-2 S log h) ≤ eTerm nl nh lhi` for `nl ≤ 2^QS S ≤ nh`, `S ≤ 0`, `2^P log h ≤ lhi`. -/
theorem eTerm_ge {nl nh lhi : ℤ} {S v : ℝ} (hS : S ≤ 0) (hl : (nl : ℝ) ≤ 2 ^ QS * S) (hh : 2 ^ QS * S ≤ (nh : ℝ))
    (hv : 2 ^ P * v ≤ (lhi : ℝ)) : 2 ^ (P + QS) * (-2 * S * v) ≤ (eTerm nl nh lhi : ℝ) := by
  have hPQ : (2 : ℝ) ^ (P + QS) = 2 ^ P * 2 ^ QS := pow_add 2 P QS
  have hQ : (0 : ℝ) < 2 ^ QS := by positivity
  set u : ℝ := -(2 ^ QS * S) with hu
  have hu0 : 0 ≤ u := by rw [hu]; nlinarith
  have e : (2 : ℝ) ^ (P + QS) * (-2 * S * v) = 2 * u * (2 ^ P * v) := by rw [hPQ, hu]; ring
  rw [e]
  unfold eTerm
  split_ifs with h0
  · have h0' : (0 : ℝ) ≤ lhi := by exact_mod_cast h0
    push_cast
    have h1 : u * (2 ^ P * v) ≤ u * lhi := mul_le_mul_of_nonneg_left hv hu0
    have h2 : u * lhi ≤ (-(nl : ℝ)) * lhi := mul_le_mul_of_nonneg_right (by rw [hu]; linarith) h0'
    linarith
  · have h0' : (lhi : ℝ) < 0 := by exact_mod_cast not_le.mp h0
    push_cast
    have h1 : u * (2 ^ P * v) ≤ u * lhi := mul_le_mul_of_nonneg_left hv hu0
    have h2 : u * lhi ≤ (-(nh : ℝ)) * lhi := by
      have : -(nh : ℝ) ≤ u := by rw [hu]; linarith
      nlinarith
    linarith

theorem anT_nonpos (x : ℝ) (i : ℕ) : anT x i ≤ 0 := by
  unfold anT; split_ifs with h
  · exact h.2.le
  · exact le_rfl

/-- **The U bounds** from end-point data `A` at `p` and `B` at `q` (any data with these properties). -/
theorem uP_core {Xp Xq k : ℕ} (hpq : Xp < Xq) (A B : EPt)
    (hAU : 2 ^ P * UR ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) ≤ (A.uhi : ℝ))
    (hB1 : (B.apl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hB2 : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (B.aph : ℝ)) :
    2 ^ P * (∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else
        CR i * Hk (eR i - (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)))) ≤
      ((A.uhi - fdiv (imul (B.apl, B.aph) (yEncl (Xq - Xp) (logT TAB L2 (Xq - Xp) 1)
          (logT TAB L2 (DEC * 2 ^ k) 1))).1 (DEC * 2 ^ k * (DEC * 2 ^ k) * 2 ^ (QS + 2)) : ℤ) : ℝ) := by
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hpqR : (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) < (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) :=
    div_lt_div_of_pos_right (by exact_mod_cast hpq) hDR
  have hH : 0 < Xq - Xp := by omega
  generalize hp : (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) = p at hAU hpqR ⊢
  generalize hq : (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) = q at hB1 hB2 hpqR
  generalize hS : ∑ i ∈ Finset.range (NN + 1), apT q i = Sq at hB1 hB2
  -- the singular terms: `C_i > 0` at `q` (the ones at `p` vanish)
  have hdec : ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) =
      UR p - Sq * Hk (q - p) := by
    rw [UR, ← hS, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold apT
    have hsi : singI k Xp Xq i ↔ 0 < CR i ∧ (eR i = p ∨ eR i = q) := by rw [singI_iff, hp, hq]
    by_cases hs : singI k Xp Xq i
    · rw [if_pos hs]
      obtain ⟨hC, hpq'⟩ := hsi.mp hs
      rcases hpq' with h | h
      · rw [if_neg (fun h' => by rw [h] at h'; exact hpqR.ne h'.1), h, sub_self, Hk_zero]; ring
      · rw [if_pos ⟨h, hC⟩, h]; ring
    · rw [if_neg hs]
      rw [if_neg (fun h' => hs (hsi.mpr ⟨h'.2, Or.inr h'.1⟩))]
      ring
  rw [hdec]
  have hLDs := logT_D k
  have ht : |q - p| = ((Xq - Xp : ℕ) : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) := by
    rw [abs_of_pos (by linarith), Nat.cast_sub hpq.le, ← hp, ← hq, sub_div]
  have hY := yEncl_spec hH hD hLDs ht
  have hm := imul_spec (a := (B.apl, B.aph)) (x := 2 ^ QS * Sq) ⟨hB1, hB2⟩ hY
  have hden : 0 < DEC * 2 ^ k * (DEC * 2 ^ k) * 2 ^ (QS + 2) := by positivity
  have hf := fdiv_le ((imul (B.apl, B.aph) (yEncl (Xq - Xp) (logT TAB L2 (Xq - Xp) 1)
    (logT TAB L2 (DEC * 2 ^ k) 1))).1) hden
  have hPQ : (2 : ℝ) ^ (QS + 2) = 2 ^ QS * 4 := by rw [pow_add]; norm_num
  have hcorr : ((fdiv (imul (B.apl, B.aph) (yEncl (Xq - Xp) (logT TAB L2 (Xq - Xp) 1)
      (logT TAB L2 (DEC * 2 ^ k) 1))).1 (DEC * 2 ^ k * (DEC * 2 ^ k) * 2 ^ (QS + 2)) : ℤ) : ℝ) ≤
      2 ^ P * (Sq * Hk (q - p)) := by
    refine le_trans hf ?_
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    push_cast
    rw [hPQ]
    have e : 2 ^ P * (Sq * Hk (q - p)) * (((DEC : ℝ) * 2 ^ k) * ((DEC : ℝ) * 2 ^ k) * (2 ^ QS * 4)) =
        (2 ^ QS * Sq) * (4 * 2 ^ P * (((DEC * 2 ^ k : ℕ) : ℝ)) ^ 2 * Hk (q - p)) := by push_cast; ring
    rw [e]
    exact hm.1
  push_cast
  linarith

theorem uQ_core {Xp Xq k : ℕ} (hpq : Xp < Xq) (A B : EPt)
    (hBU : 2 ^ P * UR ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) ≤ (B.uhi : ℝ))
    (hA1 : (A.apl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hA2 : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (A.aph : ℝ)) :
    2 ^ P * (∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else
        CR i * Hk (eR i - (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)))) ≤
      ((B.uhi - fdiv (imul (A.apl, A.aph) (yEncl (Xq - Xp) (logT TAB L2 (Xq - Xp) 1)
          (logT TAB L2 (DEC * 2 ^ k) 1))).1 (DEC * 2 ^ k * (DEC * 2 ^ k) * 2 ^ (QS + 2)) : ℤ) : ℝ) := by
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hpqR : (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) < (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) :=
    div_lt_div_of_pos_right (by exact_mod_cast hpq) hDR
  have hH : 0 < Xq - Xp := by omega
  generalize hp : (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) = p at hA1 hA2 hpqR
  generalize hq : (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) = q at hBU hpqR ⊢
  generalize hS : ∑ i ∈ Finset.range (NN + 1), apT p i = Sp at hA1 hA2
  have hdec : ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) =
      UR q - Sp * Hk (p - q) := by
    rw [UR, ← hS, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold apT
    have hsi : singI k Xp Xq i ↔ 0 < CR i ∧ (eR i = p ∨ eR i = q) := by rw [singI_iff, hp, hq]
    by_cases hs : singI k Xp Xq i
    · rw [if_pos hs]
      obtain ⟨hC, hpq'⟩ := hsi.mp hs
      rcases hpq' with h | h
      · rw [if_pos ⟨h, hC⟩, h]; ring
      · rw [if_neg (fun h' => by rw [h] at h'; exact hpqR.ne' h'.1), h, sub_self, Hk_zero]; ring
    · rw [if_neg hs]
      rw [if_neg (fun h' => hs (hsi.mpr ⟨h'.2, Or.inl h'.1⟩))]
      ring
  rw [hdec]
  have hLDs := logT_D k
  have ht : |p - q| = ((Xq - Xp : ℕ) : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) := by
    rw [abs_sub_comm, abs_of_pos (by linarith), Nat.cast_sub hpq.le, ← hp, ← hq, sub_div]
  have hY := yEncl_spec hH hD hLDs ht
  have hm := imul_spec (a := (A.apl, A.aph)) (x := 2 ^ QS * Sp) ⟨hA1, hA2⟩ hY
  have hden : 0 < DEC * 2 ^ k * (DEC * 2 ^ k) * 2 ^ (QS + 2) := by positivity
  have hf := fdiv_le ((imul (A.apl, A.aph) (yEncl (Xq - Xp) (logT TAB L2 (Xq - Xp) 1)
    (logT TAB L2 (DEC * 2 ^ k) 1))).1) hden
  have hPQ : (2 : ℝ) ^ (QS + 2) = 2 ^ QS * 4 := by rw [pow_add]; norm_num
  have hcorr : ((fdiv (imul (A.apl, A.aph) (yEncl (Xq - Xp) (logT TAB L2 (Xq - Xp) 1)
      (logT TAB L2 (DEC * 2 ^ k) 1))).1 (DEC * 2 ^ k * (DEC * 2 ^ k) * 2 ^ (QS + 2)) : ℤ) : ℝ) ≤
      2 ^ P * (Sp * Hk (p - q)) := by
    refine le_trans hf ?_
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    push_cast
    rw [hPQ]
    have e : 2 ^ P * (Sp * Hk (p - q)) * (((DEC : ℝ) * 2 ^ k) * ((DEC : ℝ) * 2 ^ k) * (2 ^ QS * 4)) =
        (2 ^ QS * Sp) * (4 * 2 ^ P * (((DEC * 2 ^ k : ℕ) : ℝ)) ^ 2 * Hk (p - q)) := by push_cast; ring
    rw [e]
    exact hm.1
  push_cast
  linarith

/-- One node of the curvature sum on `(p, q)`. -/
theorem curv_node_le {p q y : ℝ} (hpq : p < q) (hy1 : p < y) (hy2 : y < q) (i : ℕ)
    (hin : CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) :
    (if 0 < CR i ∧ (eR i = p ∨ eR i = q) then 0 else -2 * CR i * Real.log |y - eR i|) ≤
      -2 * (anT p i + anT q i) * Real.log (q - p) +
        (if CR i ≠ 0 ∧ (eR i < p ∨ q < eR i) then -2 * CR i * Real.log |y - eR i| else 0) := by
  by_cases hC : CR i = 0
  · simp [anT, hC]
  · by_cases hep : eR i = p
    · have hnq : eR i ≠ q := by rw [hep]; exact hpq.ne
      have hR : ¬ (CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) := by
        rw [hep]; intro h; rcases h.2 with h' | h' <;> linarith
      rw [if_neg hR, add_zero]
      by_cases hCp : 0 < CR i
      · rw [if_pos ⟨hCp, Or.inl hep⟩]
        have ha : anT p i = 0 := by simp [anT, not_lt.mpr hCp.le]
        have hb : anT q i = 0 := by simp [anT, hnq]
        rw [ha, hb]; simp
      · have hCn : CR i < 0 := lt_of_le_of_ne (not_lt.mp hCp) hC
        rw [if_neg (fun h => hCp h.1)]
        have ha : anT p i = CR i := by simp [anT, hep, hCn]
        have hb : anT q i = 0 := by simp [anT, hnq]
        rw [ha, hb, add_zero, hep]
        have hyp : |y - p| ≤ q - p := by rw [abs_of_pos (by linarith)]; linarith
        have hlog := Real.log_le_log (abs_pos.mpr (by linarith : y - p ≠ 0)) hyp
        nlinarith
    · by_cases heq : eR i = q
      · have hR : ¬ (CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) := by
          rw [heq]; intro h; rcases h.2 with h' | h' <;> linarith
        rw [if_neg hR, add_zero]
        by_cases hCp : 0 < CR i
        · rw [if_pos ⟨hCp, Or.inr heq⟩]
          have ha : anT p i = 0 := by simp [anT, hep]
          have hb : anT q i = 0 := by simp [anT, not_lt.mpr hCp.le]
          rw [ha, hb]; simp
        · have hCn : CR i < 0 := lt_of_le_of_ne (not_lt.mp hCp) hC
          rw [if_neg (fun h => hCp h.1)]
          have ha : anT p i = 0 := by simp [anT, hep]
          have hb : anT q i = CR i := by simp [anT, heq, hCn]
          rw [ha, hb, zero_add, heq]
          have hyq : |y - q| ≤ q - p := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
          have hlog := Real.log_le_log (abs_pos.mpr (by linarith : y - q ≠ 0)) hyq
          nlinarith
      · have hout : eR i < p ∨ q < eR i := by
          by_contra hc
          push Not at hc
          exact hin hC ⟨lt_of_le_of_ne hc.1 (Ne.symm hep), lt_of_le_of_ne hc.2 heq⟩
        have hns : ¬ (0 < CR i ∧ (eR i = p ∨ eR i = q)) := by
          rintro ⟨-, h | h⟩
          · exact hep h
          · exact heq h
        rw [if_neg hns, if_pos ⟨hC, hout⟩]
        have ha : anT p i = 0 := by simp [anT, hep]
        have hb : anT q i = 0 := by simp [anT, heq]
        rw [ha, hb]; simp

/-- The log sum at `p` without the nodes at `p`, split into the nodes outside `[p, q]` and those at `q`. -/
theorem gT_split_p {p q : ℝ} (hpq : p < q) (i : ℕ) (hin : CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) :
    gT p i = (if CR i ≠ 0 ∧ (eR i < p ∨ q < eR i) then CR i * Real.log |p - eR i| else 0) +
      (apT q i + anT q i) * Real.log (q - p) := by
  by_cases hC : CR i = 0
  · simp [gT, apT, anT, hC]
  · by_cases hep : eR i = p
    · have hnq : eR i ≠ q := by rw [hep]; exact hpq.ne
      have hR : ¬ (CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) := by
        rw [hep]; intro h; rcases h.2 with h' | h' <;> linarith
      simp [gT, apT, anT, hep, hnq, hR, hpq.ne]
    · by_cases heq : eR i = q
      · have hR : ¬ (CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) := by
          rw [heq]; intro h; rcases h.2 with h' | h' <;> linarith
        have habs : |p - eR i| = q - p := by rw [heq, abs_sub_comm, abs_of_pos (by linarith)]
        rw [if_neg hR, zero_add]
        unfold gT apT anT
        rw [if_neg hep, habs]
        rcases lt_or_gt_of_ne hC with hCn | hCp
        · rw [if_neg (fun h => absurd h.2 (not_lt.mpr hCn.le)), if_pos ⟨heq, hCn⟩]; ring
        · rw [if_pos ⟨heq, hCp⟩, if_neg (fun h => absurd h.2 (not_lt.mpr hCp.le))]; ring
      · have hout : eR i < p ∨ q < eR i := by
          by_contra hc
          push Not at hc
          exact hin hC ⟨lt_of_le_of_ne hc.1 (Ne.symm hep), lt_of_le_of_ne hc.2 heq⟩
        rw [if_pos ⟨hC, hout⟩]
        simp [gT, apT, anT, hep, heq, abs_sub_comm]

theorem gT_split_q {p q : ℝ} (hpq : p < q) (i : ℕ) (hin : CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) :
    gT q i = (if CR i ≠ 0 ∧ (eR i < p ∨ q < eR i) then CR i * Real.log |q - eR i| else 0) +
      (apT p i + anT p i) * Real.log (q - p) := by
  by_cases hC : CR i = 0
  · simp [gT, apT, anT, hC]
  · by_cases heq : eR i = q
    · have hnp : eR i ≠ p := by rw [heq]; exact hpq.ne'
      have hR : ¬ (CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) := by
        rw [heq]; intro h; rcases h.2 with h' | h' <;> linarith
      simp [gT, apT, anT, heq, hnp, hR, hpq.ne']
    · by_cases hep : eR i = p
      · have hR : ¬ (CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) := by
          rw [hep]; intro h; rcases h.2 with h' | h' <;> linarith
        have habs : |q - eR i| = q - p := by rw [hep, abs_of_pos (by linarith)]
        rw [if_neg hR, zero_add]
        unfold gT apT anT
        rw [if_neg heq, habs]
        rcases lt_or_gt_of_ne hC with hCn | hCp
        · rw [if_neg (fun h => absurd h.2 (not_lt.mpr hCn.le)), if_pos ⟨hep, hCn⟩]; ring
        · rw [if_pos ⟨hep, hCp⟩, if_neg (fun h => absurd h.2 (not_lt.mpr hCp.le))]; ring
      · have hout : eR i < p ∨ q < eR i := by
          by_contra hc
          push Not at hc
          exact hin hC ⟨lt_of_le_of_ne hc.1 (Ne.symm hep), lt_of_le_of_ne hc.2 heq⟩
        rw [if_pos ⟨hC, hout⟩]
        simp [gT, apT, anT, hep, heq, abs_sub_comm]

/-- The `K` weights of the nodes outside `[p, q]`: `klT` at `p` plus `krT` at `q`. -/
theorem kappa_split {p q : ℝ} (hpq : p < q) (i : ℕ) (hin : CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) :
    (if CR i ≠ 0 ∧ (eR i < p ∨ q < eR i) then (if CR i < 0 then 2 * |CR i| / distPQ p q (eR i) ^ 2 else 0) else 0) =
      klT p i + krT q i := by
  by_cases hC : CR i = 0
  · simp [klT, krT, hC]
  · by_cases hout : eR i < p ∨ q < eR i
    · rw [if_pos ⟨hC, hout⟩]
      rcases hout with h | h
      · have h' : ¬ q < eR i := not_lt.mpr (by linarith)
        have hd : distPQ p q (eR i) = p - eR i := by simp [distPQ, h]
        have hsq : (p - eR i) ^ 2 = (eR i - p) ^ 2 := by ring
        by_cases hCn : CR i < 0
        · simp [klT, krT, hCn, h, h', hd, hsq]
        · simp [klT, krT, hCn]
      · have h' : ¬ eR i < p := not_lt.mpr (by linarith)
        have hd : distPQ p q (eR i) = eR i - q := by simp [distPQ, h']
        have hsq : (q - eR i) ^ 2 = (eR i - q) ^ 2 := by ring
        by_cases hCn : CR i < 0
        · simp [klT, krT, hCn, h, h', hd, hsq]
        · simp [klT, krT, hCn]
    · rw [if_neg (fun h => hout h.2)]
      push Not at hout
      simp [klT, krT, not_lt.mpr hout.1, not_lt.mpr hout.2]

set_option maxRecDepth 200000 in
/-- **The curvature bound.** The node part of the curvature of `A` on `(p, q)` is at most `m / 2^(P+QS)`. -/
theorem mE_core {Xp Xq k : ℕ} (hpq : Xp < Xq) (A B : EPt)
    (hnin : ∀ i ≤ NN, CR i ≠ 0 → ¬ ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) < eR i ∧ eR i < (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)))
    (hAg : (A.g0 : ℝ) ≤ 2 ^ (P + QS) * ∑ i ∈ Finset.range (NN + 1), gT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hAkl : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), klT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (A.kl : ℝ))
    (hAp1 : (A.apl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hAp2 : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (A.aph : ℝ))
    (hAn1 : (A.anl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hAn2 : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (A.anh : ℝ))
    (hBg : (B.g0 : ℝ) ≤ 2 ^ (P + QS) * ∑ i ∈ Finset.range (NN + 1), gT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hBkr : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), krT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (B.kr : ℝ))
    (hBp1 : (B.apl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hBp2 : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (B.aph : ℝ))
    (hBn1 : (B.anl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i)
    (hBn2 : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ (B.anh : ℝ)) :
    ∀ y : ℝ, (Xp : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) < y → y < (Xq : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) →
      2 ^ (P + QS) * ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |y - eR i|) ≤
        ((eTerm A.anl A.anh ((logT TAB L2 (Xq - Xp) 1).2 - (logT TAB L2 (DEC * 2 ^ k) 1).1) +
          eTerm B.anl B.anh ((logT TAB L2 (Xq - Xp) 1).2 - (logT TAB L2 (DEC * 2 ^ k) 1).1) +
          max (-2 * (A.g0 - (imul (B.apl + B.anl, B.aph + B.anh) ((logT TAB L2 (Xq - Xp) 1).1 -
              (logT TAB L2 (DEC * 2 ^ k) 1).2, (logT TAB L2 (Xq - Xp) 1).2 - (logT TAB L2 (DEC * 2 ^ k) 1).1)).2))
            (-2 * (B.g0 - (imul (A.apl + A.anl, A.aph + A.anh) ((logT TAB L2 (Xq - Xp) 1).1 -
              (logT TAB L2 (DEC * 2 ^ k) 1).2, (logT TAB L2 (Xq - Xp) 1).2 - (logT TAB L2 (DEC * 2 ^ k) 1).1)).2)) +
          cdiv ((A.kl + B.kr) * (((Xq - Xp) * (Xq - Xp) : ℕ) : ℤ) * 2 ^ P) (8 * (DEC * 2 ^ k) * (DEC * 2 ^ k)) : ℤ) : ℝ) := by
  intro y hy1 hy2
  set D : ℕ := DEC * 2 ^ k with hDdef
  set p : ℝ := (Xp : ℝ) / (D : ℝ) with hpdef
  set q : ℝ := (Xq : ℝ) / (D : ℝ) with hqdef
  set H : ℕ := Xq - Xp with hHdef
  set LD := logT TAB L2 D 1 with hLDdef
  set Lh := logT TAB L2 H 1 with hLhdef
  have hD : 0 < D := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hpqR : p < q := div_lt_div_of_pos_right (by exact_mod_cast hpq) hDR
  have hH : 0 < H := by omega
  have hHR : (H : ℝ) / D = q - p := by rw [hHdef, Nat.cast_sub hpq.le, sub_div]
  have hPQ : (2 : ℝ) ^ (P + QS) = 2 ^ P * 2 ^ QS := pow_add 2 P QS
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hQ : (0 : ℝ) < 2 ^ QS := by positivity
  -- `log h`
  have hLDs := logT_D k
  obtain ⟨hLh1, hLh2⟩ := logT_sound (a := H) (b := 1) hH one_pos
  simp only [Nat.cast_one, div_one] at hLh1 hLh2
  have hlogh : Real.log (q - p) = Real.log H - Real.log D := by
    rw [← hHR, Real.log_div (by exact_mod_cast hH.ne') hDR.ne']
  have hlh : (((Lh.1 - LD.2 : ℤ)) : ℝ) ≤ 2 ^ P * Real.log (q - p) ∧
      2 ^ P * Real.log (q - p) ≤ (((Lh.2 - LD.1 : ℤ)) : ℝ) := by
    rw [hlogh, mul_sub]; push_cast
    constructor <;> linarith [hLDs.1, hLDs.2, hLh1, hLh2]
  -- the end-point data
  set Spn : ℝ := ∑ i ∈ Finset.range (NN + 1), anT p i with hSpn
  set Sqn : ℝ := ∑ i ∈ Finset.range (NN + 1), anT q i with hSqn
  set Spp : ℝ := ∑ i ∈ Finset.range (NN + 1), apT p i with hSpp
  set Sqp : ℝ := ∑ i ∈ Finset.range (NN + 1), apT q i with hSqp
  set R : Finset ℕ := (Finset.range (NN + 1)).filter (fun i => CR i ≠ 0 ∧ (eR i < p ∨ q < eR i)) with hR
  have hin : ∀ i ∈ Finset.range (NN + 1), CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q) := by
    intro i hi; exact hnin i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  -- the summand, node by node
  have hsing : ∀ i, singI k Xp Xq i ↔ 0 < CR i ∧ (eR i = p ∨ eR i = q) := fun i => singI_iff
  have hsum : ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |y - eR i|) ≤
      -2 * (Spn + Sqn) * Real.log (q - p) + ∑ i ∈ R, -2 * CR i * Real.log |y - eR i| := by
    have h1 : ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |y - eR i|) ≤
        ∑ i ∈ Finset.range (NN + 1), (-2 * (anT p i + anT q i) * Real.log (q - p) +
          (if CR i ≠ 0 ∧ (eR i < p ∨ q < eR i) then -2 * CR i * Real.log |y - eR i| else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      have := curv_node_le hpqR hy1 hy2 i (hin i hi)
      simp only [hsing]
      exact this
    refine le_trans h1 (le_of_eq ?_)
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [hSpn, hSqn, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      try (apply Finset.sum_congr rfl; intro i _; ring)
    · rw [hR, Finset.sum_filter]
  -- the second-order bound on `R`
  set κ : ℕ → ℝ := fun i => if CR i < 0 then 2 * |CR i| / distPQ p q (eR i) ^ 2 else 0 with hκdef
  have hRout : ∀ i ∈ R, eR i < p ∨ q < eR i := by
    intro i hi; simp only [hR, Finset.mem_filter] at hi; exact hi.2.2
  have hdist : ∀ i ∈ R, 0 < distPQ p q (eR i) := by
    intro i hi
    unfold distPQ
    rcases hRout i hi with h | h
    · rw [if_pos h]; linarith
    · rw [if_neg (not_lt.mpr (by linarith))]; linarith
  have hκ0 : ∀ i ∈ R, 0 ≤ κ i := by
    intro i hi; simp only [hκdef]; split_ifs
    · have := hdist i hi; positivity
    · exact le_rfl
  have hκc : ∀ i ∈ R, -2 * CR i ≤ κ i * distPQ p q (eR i) ^ 2 := by
    intro i hi
    simp only [hκdef]
    split_ifs with hCn
    · have := hdist i hi
      rw [div_mul_cancel₀ _ (by positivity), abs_of_neg hCn]
      linarith
    · simp only [zero_mul]; linarith [not_lt.mp hCn]
  have hso := second_order_le hpqR R CR eR κ hRout hκ0 hκc ⟨hy1.le, hy2.le⟩
  -- the end-point values of the `R`-sum from `g0`
  have hsgp : ∑ i ∈ Finset.range (NN + 1), gT p i =
      ∑ i ∈ R, CR i * Real.log |p - eR i| + (Sqp + Sqn) * Real.log (q - p) := by
    rw [Finset.sum_congr rfl (fun i hi => gT_split_p hpqR i (hin i hi)), Finset.sum_add_distrib, hR, Finset.sum_filter,
      ← Finset.sum_mul, Finset.sum_add_distrib]
  have hsgq : ∑ i ∈ Finset.range (NN + 1), gT q i =
      ∑ i ∈ R, CR i * Real.log |q - eR i| + (Spp + Spn) * Real.log (q - p) := by
    rw [Finset.sum_congr rfl (fun i hi => gT_split_q hpqR i (hin i hi)), Finset.sum_add_distrib, hR, Finset.sum_filter,
      ← Finset.sum_mul, Finset.sum_add_distrib]
  have hmq := imul_spec (a := (B.apl + B.anl, B.aph + B.anh))
    (b := (Lh.1 - LD.2, Lh.2 - LD.1)) (x := 2 ^ QS * (Sqp + Sqn)) ⟨by push_cast; linarith, by push_cast; linarith⟩ hlh
  have hmp := imul_spec (a := (A.apl + A.anl, A.aph + A.anh))
    (b := (Lh.1 - LD.2, Lh.2 - LD.1)) (x := 2 ^ QS * (Spp + Spn)) ⟨by push_cast; linarith, by push_cast; linarith⟩ hlh
  have hphip : 2 ^ (P + QS) * ∑ i ∈ R, -2 * CR i * Real.log |p - eR i| ≤
      ((-2 * (A.g0 - (imul (B.apl + B.anl, B.aph + B.anh) (Lh.1 - LD.2, Lh.2 - LD.1)).2) : ℤ) : ℝ) := by
    have e : ∑ i ∈ R, -2 * CR i * Real.log |p - eR i| = -2 * ∑ i ∈ R, CR i * Real.log |p - eR i| := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    push_cast
    have h1 : (A.g0 : ℝ) ≤ 2 ^ (P + QS) * (∑ i ∈ R, CR i * Real.log |p - eR i| + (Sqp + Sqn) * Real.log (q - p)) := by
      rw [← hsgp]; exact hAg
    have h2 : (2 ^ QS * (Sqp + Sqn)) * (2 ^ P * Real.log (q - p)) ≤
        ((imul (B.apl + B.anl, B.aph + B.anh) (Lh.1 - LD.2, Lh.2 - LD.1)).2 : ℝ) := hmq.2
    rw [hPQ] at h1 ⊢
    linarith
  have hphiq : 2 ^ (P + QS) * ∑ i ∈ R, -2 * CR i * Real.log |q - eR i| ≤
      ((-2 * (B.g0 - (imul (A.apl + A.anl, A.aph + A.anh) (Lh.1 - LD.2, Lh.2 - LD.1)).2) : ℤ) : ℝ) := by
    have e : ∑ i ∈ R, -2 * CR i * Real.log |q - eR i| = -2 * ∑ i ∈ R, CR i * Real.log |q - eR i| := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    push_cast
    have h1 : (B.g0 : ℝ) ≤ 2 ^ (P + QS) * (∑ i ∈ R, CR i * Real.log |q - eR i| + (Spp + Spn) * Real.log (q - p)) := by
      rw [← hsgq]; exact hBg
    have h2 : (2 ^ QS * (Spp + Spn)) * (2 ^ P * Real.log (q - p)) ≤
        ((imul (A.apl + A.anl, A.aph + A.anh) (Lh.1 - LD.2, Lh.2 - LD.1)).2 : ℝ) := hmp.2
    rw [hPQ] at h1 ⊢
    linarith
  -- `∑ κ ≤ (kl + kr) / 2^QS`
  have hκsum : 2 ^ QS * ∑ i ∈ R, κ i ≤ ((A.kl + B.kr : ℤ) : ℝ) := by
    have e : ∑ i ∈ R, κ i = ∑ i ∈ Finset.range (NN + 1), klT p i + ∑ i ∈ Finset.range (NN + 1), krT q i := by
      rw [hR, Finset.sum_filter, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i hi => kappa_split hpqR i (hin i hi))
    rw [e, mul_add]; push_cast; linarith
  have hK0 : 0 ≤ ∑ i ∈ R, κ i := Finset.sum_nonneg hκ0
  have hden : 0 < 8 * D * D := by positivity
  have hKt := le_cdiv ((A.kl + B.kr) * ((H * H : ℕ) : ℤ) * 2 ^ P) hden
  have hKt' : 2 ^ (P + QS) * ((∑ i ∈ R, κ i) * (q - p) ^ 2 / 8) ≤
      (cdiv ((A.kl + B.kr) * ((H * H : ℕ) : ℤ) * 2 ^ P) (8 * D * D) : ℝ) := by
    refine le_trans ?_ hKt
    rw [le_div_iff₀ (by exact_mod_cast hden), ← hHR]
    push_cast
    have e : 2 ^ (P + QS) * ((∑ i ∈ R, κ i) * ((H : ℝ) / D) ^ 2 / 8) * (8 * D * D) =
        (2 ^ QS * ∑ i ∈ R, κ i) * ((H : ℝ) * H * 2 ^ P) := by
      rw [hPQ]; field_simp
    rw [e]
    have hHH : (0 : ℝ) ≤ (H : ℝ) * H * 2 ^ P := by positivity
    have := mul_le_mul_of_nonneg_right hκsum hHH
    push_cast at this
    linarith
  -- the terms at the end points
  have hEA := eTerm_ge (nl := A.anl) (nh := A.anh) (lhi := Lh.2 - LD.1) (S := Spn) (v := Real.log (q - p))
    (Finset.sum_nonpos (fun i _ => anT_nonpos p i)) hAn1 hAn2 hlh.2
  have hEB := eTerm_ge (nl := B.anl) (nh := B.anh) (lhi := Lh.2 - LD.1) (S := Sqn) (v := Real.log (q - p))
    (Finset.sum_nonpos (fun i _ => anT_nonpos q i)) hBn1 hBn2 hlh.2
  -- combine
  have hmax : 2 ^ (P + QS) * max (∑ i ∈ R, -2 * CR i * Real.log |p - eR i|) (∑ i ∈ R, -2 * CR i * Real.log |q - eR i|) ≤
      max (((-2 * (A.g0 - (imul (B.apl + B.anl, B.aph + B.anh) (Lh.1 - LD.2, Lh.2 - LD.1)).2) : ℤ) : ℝ))
        (((-2 * (B.g0 - (imul (A.apl + A.anl, A.aph + A.anh) (Lh.1 - LD.2, Lh.2 - LD.1)).2) : ℤ) : ℝ)) := by
    rw [mul_max_of_nonneg _ _ (by positivity)]
    exact max_le_max hphip hphiq
  have hsum' := mul_le_mul_of_nonneg_left (le_trans hsum (add_le_add le_rfl hso)) (by positivity : (0 : ℝ) ≤ 2 ^ (P + QS))
  push_cast
  push_cast at hmax
  have e1 : (2 : ℝ) ^ (P + QS) * (-2 * (Spn + Sqn) * Real.log (q - p) +
      (max (∑ i ∈ R, -2 * CR i * Real.log |p - eR i|) (∑ i ∈ R, -2 * CR i * Real.log |q - eR i|) +
        (∑ i ∈ R, κ i) * (q - p) ^ 2 / 8)) =
      2 ^ (P + QS) * (-2 * Spn * Real.log (q - p)) + 2 ^ (P + QS) * (-2 * Sqn * Real.log (q - p)) +
      2 ^ (P + QS) * max (∑ i ∈ R, -2 * CR i * Real.log |p - eR i|) (∑ i ∈ R, -2 * CR i * Real.log |q - eR i|) +
      2 ^ (P + QS) * ((∑ i ∈ R, κ i) * (q - p) ^ 2 / 8) := by ring
  rw [e1] at hsum'
  push_cast at hEA hEB hKt'
  linarith

end Trace86.Cert
