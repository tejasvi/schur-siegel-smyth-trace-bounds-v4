import Trace86U.CheckSound9

/-!
# Soundness of condition (M) of the 86a upper bound: root brackets and the moment bound

For `Q = Qd q` with brackets `bs` (scale `D = 10^12 2^k`) passing `momentOK`: every bracket holds a root (`bracket_root`,
intermediate value theorem, or an exact rational root), the brackets are ordered, so the chosen roots are distinct, and
there are `deg Q` of them: they are all the roots (`roots_eq`). The checker's bound gives
`∑_r (c₀ - 2 U'(r)) > 0` over these roots (`moment_one`), i.e. `∑_r (U_{μ₀}(r) + c₀) > 0`.
-/

open Polynomial Set

namespace Trace86.UCert

open T86UCore AuxCore AuxCommon

theorem polyVal_spec {D : ℕ} (hD : 0 < D) (q : List ℤ) (X : ℕ) :
    ((polyVal q X D : ℤ) : ℝ) = (D : ℝ) ^ (q.length - 1) * (QR q).eval ((X : ℝ) / D) := by
  have h := taylorR_spec hD X q 0
  rw [evalAscR_zero, add_zero] at h
  exact h

theorem bracket_le {q : List ℤ} {D : ℕ} {b : ℕ × ℕ} (h : bracketOK q D b = true) : b.1 ≤ b.2 := by
  unfold bracketOK at h
  split_ifs at h with heq
  · exact heq.le
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.le

theorem bracket_root {q : List ℤ} {D : ℕ} (hD : 0 < D) {b : ℕ × ℕ} (h : bracketOK q D b = true) :
    ∃ r : ℝ, (b.1 : ℝ) / D ≤ r ∧ r ≤ (b.2 : ℝ) / D ∧ (QR q).eval r = 0 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hpow : (0 : ℝ) < (D : ℝ) ^ (q.length - 1) := by positivity
  unfold bracketOK at h
  split_ifs at h with heq
  · refine ⟨(b.1 : ℝ) / D, le_rfl, by rw [heq], ?_⟩
    have h0 : polyVal q b.1 D = 0 := by simpa using h
    have h1 := polyVal_spec hD q b.1
    rw [h0, Int.cast_zero] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hpow.ne'
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, hneg⟩ := h
    have hl := polyVal_spec hD q b.1
    have hu := polyVal_spec hD q b.2
    have hab : (b.1 : ℝ) / D ≤ (b.2 : ℝ) / D :=
      div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) hDR.le
    have hcont : ContinuousOn (fun x => (QR q).eval x) (Icc ((b.1 : ℝ) / D) ((b.2 : ℝ) / D)) :=
      (QR q).continuous.continuousOn
    have hneg' : ((polyVal q b.1 D : ℤ) : ℝ) * ((polyVal q b.2 D : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
    rw [hl, hu] at hneg'
    have hprod : (QR q).eval ((b.1 : ℝ) / D) * (QR q).eval ((b.2 : ℝ) / D) < 0 := by
      have e : (D : ℝ) ^ (q.length - 1) * (QR q).eval ((b.1 : ℝ) / D) *
          ((D : ℝ) ^ (q.length - 1) * (QR q).eval ((b.2 : ℝ) / D)) =
          ((D : ℝ) ^ (q.length - 1)) ^ 2 * ((QR q).eval ((b.1 : ℝ) / D) * (QR q).eval ((b.2 : ℝ) / D)) := by
        ring
      rw [e] at hneg'
      by_contra hc
      push Not at hc
      have := mul_nonneg (pow_nonneg hpow.le 2) hc
      linarith
    rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hab hcont ⟨h2.le, h1.le⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hab hcont ⟨h1.le, h2.le⟩
      exact ⟨r, hr.1, hr.2, hr0⟩

open Classical in
/-- A root in the bracket `b` (chosen). -/
noncomputable def rootOf (q : List ℤ) (D : ℕ) (b : ℕ × ℕ) : ℝ :=
  if h : 0 < D ∧ bracketOK q D b = true then Classical.choose (bracket_root h.1 h.2) else 0

theorem rootOf_spec {q : List ℤ} {D : ℕ} (hD : 0 < D) {b : ℕ × ℕ} (h : bracketOK q D b = true) :
    (b.1 : ℝ) / D ≤ rootOf q D b ∧ rootOf q D b ≤ (b.2 : ℝ) / D ∧ (QR q).eval (rootOf q D b) = 0 := by
  unfold rootOf
  rw [dif_pos ⟨hD, h⟩]
  exact Classical.choose_spec (bracket_root hD h)

theorem bracketsOrdered_pairwise : ∀ (bs : List (ℕ × ℕ)), bracketsOrdered bs = true →
    (∀ b ∈ bs, b.1 ≤ b.2) → bs.Pairwise (fun x y => x.2 < y.1)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | b1 :: b2 :: bs, h, hle => by
    simp only [bracketsOrdered, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h12, hrest⟩ := h
    have ih := bracketsOrdered_pairwise (b2 :: bs) hrest (fun b hb => hle b (List.mem_cons_of_mem _ hb))
    refine List.Pairwise.cons ?_ ih
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h12
    · have h2y := List.rel_of_pairwise_cons ih hy
      have hb2 := hle b2 (by simp)
      omega

theorem roots_pairwise {q : List ℤ} {D : ℕ} (hD : 0 < D) {bs : List (ℕ × ℕ)}
    (hok : ∀ b ∈ bs, bracketOK q D b = true) (hord : bs.Pairwise (fun x y => x.2 < y.1)) :
    (bs.map (rootOf q D)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  refine hord.imp_of_mem ?_
  intro x y hx hy hxy
  have h1 := (rootOf_spec hD (hok x hx)).2.1
  have h2 := (rootOf_spec hD (hok y hy)).1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have : (x.2 : ℝ) / D < (y.1 : ℝ) / D := div_lt_div_of_pos_right (by exact_mod_cast hxy) hDR
  linarith

theorem roots_eq {q : List ℤ} {D : ℕ} (hD : 0 < D) {bs : List (ℕ × ℕ)}
    (hok : ∀ b ∈ bs, bracketOK q D b = true) (hord : bracketsOrdered bs = true) (hlen : bs.length = q.length - 1)
    (hq0 : QR q ≠ 0) (hdeg : (QR q).natDegree = q.length - 1) :
    (QR q).roots = ((bs.map (rootOf q D) : List ℝ) : Multiset ℝ) := by
  have hpw := roots_pairwise hD hok (bracketsOrdered_pairwise bs hord (fun b hb => bracket_le (hok b hb)))
  have hnd : (bs.map (rootOf q D)).Nodup := hpw.imp (fun h => ne_of_lt h)
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)]
    intro r hr
    rw [Multiset.mem_coe, List.mem_map] at hr
    obtain ⟨b, hb, rfl⟩ := hr
    rw [mem_roots hq0]
    exact (rootOf_spec hD (hok b hb)).2.2
  · rw [Multiset.coe_card, List.length_map, hlen, ← hdeg]
    exact card_roots' _

theorem momentLB_eq (k : ℕ) (bs : List (ℕ × ℕ)) : momentLB mkCtx k bs =
    bs.foldl (fun (acc : ℤ) (b : ℕ × ℕ) => acc + (mkCtx.isLo - mkCtx.m0hi -
      2 * (uHi (pointPass TAB L2 mkRecs k b.1 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) +
        cdiv (((47 * sumAbsC mkRecs * (b.2 - b.1) : ℕ) : ℤ) * 2 ^ P) (DEC * 2 ^ k * 2 ^ QS)))) 0 := by
  simp only [momentLB, ctx_tab, ctx_l2, ctx_rs, ctx_sumC]

/-- One bracket: the checker's term is at most `2^P (c₀ - 2 U'(r))` at the chosen root. -/
theorem bracket_term_le {q : List ℤ} {k : ℕ} {b : ℕ × ℕ} (hok : bracketOK q (DEC * 2 ^ k) b = true)
    (h6 : b.2 ≤ 6 * (DEC * 2 ^ k)) :
    (((mkCtx.isLo - mkCtx.m0hi -
      2 * (uHi (pointPass TAB L2 mkRecs k b.1 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) +
        cdiv (((47 * sumAbsC mkRecs * (b.2 - b.1) : ℕ) : ℤ) * 2 ^ P) (DEC * 2 ^ k * 2 ^ QS))) : ℤ) : ℝ) ≤
      2 ^ P * (c0R - 2 * UR (rootOf q (DEC * 2 ^ k) b)) := by
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hQS : (0 : ℝ) < 2 ^ QS := by positivity
  obtain ⟨hr1, hr2, -⟩ := rootOf_spec hD hok
  have hle := bracket_le hok
  have hLDs := logT_D k
  have hU0 : 2 ^ P * UR (b.1 / (DEC * 2 ^ k : ℕ)) ≤
      (uHi (pointPass TAB L2 (mkRecs) k b.1 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) : ℝ) :=
    uHi_le_of hD (pointPass_sound (X := b.1) hLDs).2
  have hsC := sumC_ge
  have hdU := le_cdiv (((47 * sumAbsC (mkRecs) * (b.2 - b.1) : ℕ) : ℤ) * 2 ^ P)
    (b := DEC * 2 ^ k * 2 ^ QS) (Nat.mul_pos hD (Nat.two_pow_pos QS))
  have h2 := isLo_le
  have h3 := m0hi_eq
  generalize uHi (pointPass TAB L2 (mkRecs) k b.1 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) = uh at hU0 ⊢
  generalize cdiv (((47 * sumAbsC (mkRecs) * (b.2 - b.1) : ℕ) : ℤ) * 2 ^ P)
    (DEC * 2 ^ k * 2 ^ QS) = dU at hdU ⊢
  generalize sumAbsC (mkRecs) = sC at hsC hdU
  generalize hrdef : rootOf q (DEC * 2 ^ k) b = r at hr1 hr2 ⊢
  set D : ℕ := DEC * 2 ^ k with hDdef
  set Hn : ℕ := b.2 - b.1 with hHn
  set u : ℝ := (b.1 : ℝ) / D with hudef
  set SC : ℝ := ∑ i ∈ Finset.range (NN + 1), |CR i| with hSC
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hu0 : 0 ≤ u := div_nonneg (Nat.cast_nonneg _) hDR.le
  have hur : u ≤ r := hr1
  have hr6 : r ≤ 22 := by
    refine le_trans hr2 ?_
    rw [div_le_iff₀ hDR]
    have : (b.2 : ℝ) ≤ 6 * (D : ℝ) := by exact_mod_cast h6
    linarith
  have hHD : r - u ≤ (Hn : ℝ) / D := by
    rw [hHn, Nat.cast_sub hle, sub_div]; linarith
  have hUx : UR r ≤ UR u + 47 * SC * ((Hn : ℝ) / D) := by
    have h : UR r ≤ UR u + 47 * SC * |r - u| :=
      UR_le_add (abs_eR_sub_le (le_trans hu0 hur) hr6) (abs_eR_sub_le hu0 (le_trans hur hr6))
    rw [abs_of_nonneg (by linarith)] at h
    have := mul_le_mul_of_nonneg_left hHD (mul_nonneg (by norm_num : (0 : ℝ) ≤ 47) hSC0)
    linarith
  have hdU' : 2 ^ P * (47 * SC * ((Hn : ℝ) / D)) ≤ (dU : ℝ) := by
    refine le_trans ?_ hdU
    have hDQ : ((D * 2 ^ QS : ℕ) : ℝ) = (D : ℝ) * 2 ^ QS := by push_cast; ring
    rw [hDQ, le_div_iff₀ (mul_pos hDR hQS)]
    have e : 2 ^ P * (47 * SC * ((Hn : ℝ) / D)) * ((D : ℝ) * 2 ^ QS) =
        47 * (2 ^ QS * SC) * (Hn : ℝ) * 2 ^ P := by field_simp
    rw [e]
    push_cast
    have h47 : (0 : ℝ) ≤ 47 * (Hn : ℝ) * 2 ^ P :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hP.le
    nlinarith
  have hUxP := mul_le_mul_of_nonneg_left hUx hP.le
  push_cast
  linarith

/-- **(M) for one polynomial.** -/
theorem moment_one {q : List ℤ} {k : ℕ} {bs : List (ℕ × ℕ)} (h : momentOK mkCtx q k bs = true)
    (hq0 : QR q ≠ 0) (hdeg : (QR q).natDegree = q.length - 1) :
    (QR q).roots = ((bs.map (rootOf q (DEC * 2 ^ k)) : List ℝ) : Multiset ℝ) ∧
    (∀ r ∈ bs.map (rootOf q (DEC * 2 ^ k)), 0 ≤ r ∧ r ≤ 6) ∧
    0 < ((bs.map (rootOf q (DEC * 2 ^ k))).map (fun r => c0R - 2 * UR r)).sum := by
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  unfold momentOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hlen, hord⟩, hok⟩, h6⟩, hpos⟩ := h
  refine ⟨roots_eq hD hok hord hlen hq0 hdeg, ?_, ?_⟩
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨b, hb, rfl⟩ := hr
    obtain ⟨hr1, hr2, -⟩ := rootOf_spec hD (hok b hb)
    refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) hDR.le) hr1, le_trans hr2 ?_⟩
    rw [div_le_iff₀ hDR]
    have : (b.2 : ℝ) ≤ 6 * ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast h6 b hb
    linarith
  · rw [momentLB_eq, foldl_add_eq_sum, zero_add] at hpos
    have hposR : (0 : ℝ) < (((bs.map (fun b : ℕ × ℕ => mkCtx.isLo - mkCtx.m0hi -
        2 * (uHi (pointPass TAB L2 mkRecs k b.1 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) +
          cdiv (((47 * sumAbsC mkRecs * (b.2 - b.1) : ℕ) : ℤ) * 2 ^ P) (DEC * 2 ^ k * 2 ^ QS)))).sum : ℤ) : ℝ) := by
      exact_mod_cast hpos
    rw [Int.cast_list_sum, List.map_map] at hposR
    have hsum : ((bs.map ((fun x : ℤ => (x : ℝ)) ∘ (fun b : ℕ × ℕ => mkCtx.isLo - mkCtx.m0hi -
        2 * (uHi (pointPass TAB L2 mkRecs k b.1 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) +
          cdiv (((47 * sumAbsC mkRecs * (b.2 - b.1) : ℕ) : ℤ) * 2 ^ P) (DEC * 2 ^ k * 2 ^ QS)))))).sum ≤
        (bs.map (fun b => 2 ^ P * (c0R - 2 * UR (rootOf q (DEC * 2 ^ k) b)))).sum := by
      apply List.sum_le_sum
      intro b hb
      exact bracket_term_le (hok b hb) (h6 b hb)
    rw [List.map_map]
    have e : (bs.map (fun b => 2 ^ P * (c0R - 2 * UR (rootOf q (DEC * 2 ^ k) b)))).sum =
        2 ^ P * (bs.map ((fun r => c0R - 2 * UR r) ∘ rootOf q (DEC * 2 ^ k))).sum := by
      rw [← List.sum_map_mul_left]
      rfl
    rw [e] at hsum
    have := lt_of_lt_of_le hposR hsum
    exact pos_of_mul_pos_right this hP.le

end Trace86.UCert
