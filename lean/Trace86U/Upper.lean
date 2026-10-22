import Trace86U.UpperMeasure
import Trace86U.LeavesN
import Trace86U.TailSound2
import Trace86U.MomentSound
import Trace86U.IrredSound
import T86UN.Globals
import Trace86.TraceUpper
import Trace86.MinPrincipleProof
import AuxCommon.Integrality

/-!
# The 86a upper bound, native track (N)

Lemma U1 of the paper for `μ = (1 - ε) μ₀ + ε ω`:
* (P) `F > 0` on `(0, 6]` off the roots (left tail, the 48 tiling shards, the closed end), hence
  `h = U_μ - ∑ (1 - ε) b_j log|Q_j| = (1 - ε) F ≥ 0` on `[0, 6]` off the roots;
* the minimum principle (`MinPrinciple`, proved in Trace86/MinPrincipleProof.lean) extends `h ≥ 0` to `ℂ`;
* (M) `∫ log|Q_j| dμ = (1 - ε) ∑_r (c₀ - 2 U'(r)) > 0` (root brackets), the `Q_j` are irreducible (root sums), and (S)
  `∑ (1 - ε) b_j deg Q_j < 1`: integrality (`AuxCommon.integrable_and_integral_log_evalR_nonneg`) gives Smith's premise;
* (T) `∫ x dμ = λ_U`; Smith's theorem (`SmithThm15`, the only named hypothesis) and `trace_upper_of_measure_eq` give
  `trace_upper_N`.
-/

open Polynomial Set MeasureTheory

namespace Trace86.UCert

open T86UCore AuxCommon

/-! ## (P) -/

set_option maxRecDepth 20000 in
theorem leaves_ne_nil : leaves ≠ [] := by
  intro h
  have := leaves_length
  rw [h] at this
  simp at this

theorem FR_pos_N {x : ℝ} (hx0 : 0 < x) (hx6 : x ≤ 6) (hQx : ∀ j < 21, (QR (polys.getD j [])).eval x ≠ 0) :
    0 < FR x := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  rcases le_or_gt x ((10000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) with h1 | h1
  · have hl := T86UCore.T86UN.left_tail_ok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨hpre, hpos⟩ := hl
    have h := leftTailLB_sound hpre hx0 h1 hQx
    have : (0 : ℝ) < (leftTailLB mkCtx 10000000000 0 : ℝ) / 2 ^ P := div_pos (by exact_mod_cast hpos) hP
    linarith
  · have hrange : x ∈ Icc ((40000000000 : ℕ) / (DEC * 2 ^ 2 : ℕ) : ℝ) ((6000000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) := by
      constructor
      · have e : ((40000000000 : ℕ) / (DEC * 2 ^ 2 : ℕ) : ℝ) = ((10000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) := by
          unfold DEC
          norm_num
        rw [e]
        exact h1.le
      · have e : ((6000000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) = 6 := by
          unfold DEC
          norm_num
        rw [e]
        exact hx6
    exact leavesOK_sound_Icc leaves _ _ _ _ leaves_ne_nil leavesOK_full_N x hrange hQx

/-- The weights of Lemma U1: `w_j = (1 - ε) b_j`. -/
noncomputable def wU (j : Fin JJ) : ℝ := (1 - epsU) * cR j

theorem wU_nonneg (j : Fin JJ) : 0 ≤ wU j := mul_nonneg (by linarith [epsU_lt_one]) (cR_nonneg j)

theorem evalR_Qc (j : Fin JJ) (x : ℝ) : evalR (Qc j) x = (QR (polys.getD j [])).eval x := rfl

theorem Qc0_root : evalR (Qc ⟨0, by unfold JJ; norm_num⟩) 0 = 0 := by
  rw [evalR_Qc]
  show (QR (polys.getD 0 [])).eval 0 = 0
  rw [polys_zero, QR_eval_eq]
  simp

/-- **`h ≥ 0` on `[0, 6]` off the roots.** -/
theorem h_nonneg_06 (x : ℝ) (h0 : 0 ≤ x) (h6 : x ≤ 6) (hQ : ∀ j : Fin JJ, evalR (Qc j) x ≠ 0) :
    0 ≤ (∫ y, Real.log |x - y| ∂muU) - ∑ j, wU j * Real.log |evalR (Qc j) x| := by
  have hx0 : 0 < x := by
    rcases eq_or_lt_of_le h0 with h | h
    · exfalso
      apply hQ ⟨0, by unfold JJ; norm_num⟩
      rw [← h]
      exact Qc0_root
    · exact h
  have hQx : ∀ j < 21, (QR (polys.getD j [])).eval x ≠ 0 := fun j hj => hQ ⟨j, hj⟩
  have hF := FR_pos_N hx0 h6 hQx
  have hpot : ∫ y, Real.log |x - y| ∂muU = (1 - epsU) * (-2 * UR x) + epsU * Real.log (3 / 2) := by
    rw [← logPot_muU_real ⟨h0, h6⟩]
    congr 1
    funext y
    rw [norm_ofReal_sub]
  have hsum : ∑ j, wU j * Real.log |evalR (Qc j) x| =
      (1 - epsU) * ∑ j : Fin JJ, cR j * Real.log |(QR (polys.getD j [])).eval x| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [evalR_Qc]
    unfold wU
    ring
  rw [hpot, hsum]
  have hc := epsU_c0R
  have hFR : FR x = c0R - ∑ j : Fin JJ, cR j * Real.log |(QR (polys.getD j [])).eval x| - 2 * UR x := rfl
  have h1e : 0 < 1 - epsU := by linarith [epsU_lt_one]
  have := mul_pos h1e hF
  rw [hFR] at this
  nlinarith

/-- (S) for the weights `w_j`. -/
theorem wU_budget : ∑ j, wU j * ((Qc j).natDegree : ℝ) < 1 := by
  have hb := budget_sound T86UCore.T86UN.budget_ok
  have e : ∑ j, wU j * ((Qc j).natDegree : ℝ) =
      (1 - epsU) * ∑ j ∈ Finset.range 21, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    have h := Fin.sum_univ_eq_sum_range (fun j => (1 - epsU) * (cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ))) JJ
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold wU
    rw [natDegree_Qc, cR_eq_cj]
    ring
  rw [e]
  have h1 : 0 < 1 - epsU := by linarith [epsU_lt_one]
  have h2 : 1 - epsU ≤ 1 := by linarith [epsU_pos]
  have h3 : 0 ≤ ∑ j ∈ Finset.range 21, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _))
  nlinarith

/-- **Minimum principle**: `h ≥ 0` on `ℂ` off the roots. -/
theorem hmin_U (hM : MinPrinciple) : ∀ z : ℂ, (∀ j, (toC (Qc j)).eval z ≠ 0) →
    ∑ j, wU j * Real.log ‖(toC (Qc j)).eval z‖ ≤ ∫ y, Real.log ‖z - (y : ℂ)‖ ∂muU := by
  intro z hz
  have h := hM 0 6 (by norm_num) muU inferInstance muU_compl continuous_logPot_muU JJ Qc wU Qc_ne_zero wU_nonneg
    wU_budget (fun x h0 h6 hQ => h_nonneg_06 x h0 h6 hQ) z hz
  linarith

/-! ## (M) and irreducibility from the shards -/

theorem mom_get {j : ℕ} (hj : j < 21) :
    momentOK mkCtx (polys.getD j []) (mom.getD j (0, [])).1 (mom.getD j (0, [])).2 = true := by
  have h := T86UCore.T86UN.moments_ok
  unfold momentsOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hp : polys.length = 21 := by decide +kernel
  have hjp : j < polys.length := by rw [hp]; exact hj
  have hjm : j < mom.length := by rw [← hlen]; exact hjp
  have hz : j < (List.zip polys mom).length := by simp only [List.length_zip]; omega
  have := hall _ (List.getElem_mem hz)
  rw [List.getElem_zip] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjp, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjm, Option.getD_some]
  exact this

theorem irred_get {j : ℕ} (hj : j < 21) : irredOK (mom.getD j (0, [])).1 (mom.getD j (0, [])).2 = true := by
  have h := T86UCore.T86UN.irred_ok
  unfold irredsOK at h
  rw [List.all_eq_true] at h
  have hm : mom.length = 21 := by decide +kernel
  have hjm : j < mom.length := by rw [hm]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjm, Option.getD_some]
  exact h _ (List.getElem_mem hjm)

theorem polys_len_pos {j : ℕ} (hj : j < 21) : 0 < (polys.getD j []).length - 1 := by
  have hd : ∀ j < 21, 2 ≤ (polys.getD j []).length := by decide +kernel
  have := hd j hj
  omega

theorem QR_ne_zero_j (j : Fin JJ) : QR (polys.getD j []) ≠ 0 := by
  have h := Qc_ne_zero j
  unfold Qc at h
  unfold QR
  exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr h

theorem QR_natDegree_j (j : Fin JJ) : (QR (polys.getD j [])).natDegree = (polys.getD j []).length - 1 := by
  unfold QR
  rw [natDegree_map_eq_of_injective (RingHom.injective_int _)]
  exact natDegree_Qc j

theorem Qc_irreducible (j : Fin JJ) : Irreducible (Qc j) :=
  irreducible_of_brackets (mom_get j.isLt) (irred_get j.isLt) (Qc_monic j) (natDegree_Qc j) (polys_len_pos j.isLt)

theorem toC_Qc_eq (j : Fin JJ) : toC (Qc j) = (QR (polys.getD j [])).map Complex.ofRealHom := by
  unfold toC Qc QR
  rw [Polynomial.map_map]
  congr 1

/-- **(M)**: `∫ log |Q_j| dμ ≥ 0`. -/
theorem moment_nonneg (j : Fin JJ) : 0 ≤ ∫ x, Real.log |evalR (Qc j) x| ∂muU := by
  obtain ⟨hroots, h06, hpos⟩ := moment_one (mom_get j.isLt) (QR_ne_zero_j j) (QR_natDegree_j j)
  set q := polys.getD j [] with hq
  set rs := (mom.getD j (0, [])).2.map (rootOf q (DEC * 2 ^ (mom.getD j (0, [])).1)) with hrs
  have hsplit : (QR q).Splits := by
    rw [splits_iff_card_roots, hroots, Multiset.coe_card, QR_natDegree_j j]
    have h := mom_get j.isLt
    unfold momentOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hrs, List.length_map]
    exact h.1.1.1.1
  have hrootsC : (toC (Qc j)).roots = ((rs : Multiset ℝ)).map Complex.ofRealHom := by
    rw [toC_Qc_eq, hsplit.roots_map_of_injective Complex.ofRealHom.injective, hroots]
  have hint := integral_log_evalR hlogU (Qc_ne_zero j)
  have hlc : (Qc j).leadingCoeff = 1 := Qc_monic j
  rw [hlc] at hint
  have e1 : ((Qc j).map (Int.castRingHom ℂ)) = toC (Qc j) := rfl
  rw [e1, hrootsC] at hint
  have e2 : ∀ r ∈ rs, ∫ y, Real.log ‖((Complex.ofRealHom r : ℂ)) - (y : ℂ)‖ ∂muU = (1 - epsU) * (c0R - 2 * UR r) := by
    intro r hr
    have hr06 := h06 r hr
    have h := logPot_muU_real ⟨hr06.1, hr06.2⟩
    rw [show (Complex.ofRealHom r : ℂ) = (r : ℂ) from rfl, h]
    have := epsU_c0R
    linarith
  have hsum : (((rs : Multiset ℝ).map Complex.ofRealHom).map fun ρ => ∫ y, Real.log ‖ρ - (y : ℂ)‖ ∂muU).sum =
      (1 - epsU) * (rs.map (fun r => c0R - 2 * UR r)).sum := by
    rw [Multiset.map_map, Multiset.map_coe, Multiset.sum_coe, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact e2 r hr
  have e3 : evalR (Qc j) = fun x => ((Qc j).map (Int.castRingHom ℝ)).eval x := rfl
  rw [e3, hint, hsum]
  simp only [Int.cast_one, abs_one, Real.log_one, zero_add]
  exact mul_nonneg (by linarith [epsU_lt_one]) hpos.le

/-- `μ` does not charge the (finitely many) roots of a nonzero `Q`. -/
theorem muU_roots (Q : ℤ[X]) (hQ : Q ≠ 0) : muU {x | evalR Q x = 0} = 0 := by
  have hQR : Q.map (Int.castRingHom ℝ) ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hQ
  have hfin : {x | evalR Q x = 0}.Finite := by
    refine (Q.map (Int.castRingHom ℝ)).roots.toFinset.finite_toSet.subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (mem_roots hQR).mpr hx
  exact hfin.measure_zero muU

/-- **Smith's premise for `μ`.** -/
theorem hint_U (hM : MinPrinciple) (Q : ℤ[X]) (hQ : Q ≠ 0) :
    muU {x | evalR Q x = 0} = 0 ∧ Integrable (fun x => Real.log |evalR Q x|) muU ∧
      0 ≤ ∫ x, Real.log |evalR Q x| ∂muU :=
  ⟨muU_roots Q hQ, integrable_and_integral_log_evalR_nonneg Qc wU hlogU wU_nonneg wU_budget.le Qc_irreducible
    moment_nonneg (hmin_U hM) hQ⟩

end Trace86.UCert

namespace Trace86

open AuxCommon

/-- **Upper bound (N).** For every `ε > 0`, infinitely many totally positive algebraic integers satisfy
`tr(α) ≤ (λ_U + ε) deg(α)`; that is, `C₈₆ ≤ λ_U`. (The reviewed statement, with its hypothesis
`MinPrinciple` discharged by `Trace86.minPrinciple`; `SmithThm15` is the only hypothesis.) -/
theorem trace_upper_N (hS : SmithThm15) (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamU + ε)).Infinite :=
  trace_upper_of_measure_eq hS UCert.muU_compl (UCert.hint_U minPrinciple)
    (UCert.mean_muU T86UCore.T86UN.trace_ok) ε hε

/-- The decimal form (N): infinitely many totally positive algebraic integers satisfy `tr(α) ≤ 1.8070809 deg(α)`. -/
theorem trace_upper_dec_N (hS : SmithThm15) : (TPTraceLe (18070809 / 10000000)).Infinite := by
  have hlt : lamU < 18070809 / 10000000 := by
    unfold lamU
    norm_num
  have h := trace_upper_N hS (18070809 / 10000000 - lamU) (by linarith)
  rwa [add_sub_cancel] at h

end Trace86
