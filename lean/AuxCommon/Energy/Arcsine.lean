import Mathlib

/-!
# The arcsine (equilibrium) measure of a segment and its logarithmic potential

`arcsineMeasure c R` is the image of the normalized Lebesgue measure on `(0, 2π]` under `θ ↦ c + R cos θ`, i.e. the
arcsine law `dx / (π √(R² - (x - c)²))` on `[c - R, c + R]`, the equilibrium measure of the segment (capacity `R/2`).

`logPot_arcsineMeasure`: for `R > 0` and every `z ∈ ℂ`,
`∫ log |z - y| dω(y) = log (R/2) + arcosh ((|ζ - 1| + |ζ + 1|)/2)` with `ζ = (z - c)/R` (Joukowski: on `|w| = 1`,
`z - (c + R Re w) = -(R/2) w⁻¹ (w - w₁)(w - w₂)` with `w₁ + w₂ = 2ζ`, `w₁ w₂ = 1`, then Jensen's formula for circle
averages). Corollaries: the potential equals `log (R/2)` on `[c - R, c + R]`, is `≥ log (R/2)` on `ℂ`, and is continuous.
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal Topology

namespace AuxCommon.Energy

/-- The arcsine measure of `[c - |R|, c + |R|]`: image of the normalized Lebesgue measure on `(0, 2π]` under
`θ ↦ c + R cos θ`. -/
noncomputable def arcsineMeasure (c R : ℝ) : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • (volume.restrict (Ioc 0 (2 * π))).map (fun θ => c + R * Real.cos θ)

lemma measurable_arcsineParam (c R : ℝ) : Measurable fun θ : ℝ => c + R * Real.cos θ := by fun_prop

instance isProbabilityMeasure_arcsineMeasure (c R : ℝ) : IsProbabilityMeasure (arcsineMeasure c R) := by
  constructor
  rw [arcsineMeasure, Measure.smul_apply, Measure.map_apply (measurable_arcsineParam c R) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

/-- The arcsine measure is supported in `[c - |R|, c + |R|]`. -/
lemma arcsineMeasure_compl_Icc (c R : ℝ) : arcsineMeasure c R (Icc (c - |R|) (c + |R|))ᶜ = 0 := by
  rw [arcsineMeasure, Measure.smul_apply,
    Measure.map_apply (measurable_arcsineParam c R) measurableSet_Icc.compl]
  have : (fun θ : ℝ => c + R * Real.cos θ) ⁻¹' (Icc (c - |R|) (c + |R|))ᶜ = ∅ := by
    ext θ
    simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_empty_iff_false, iff_false, not_not]
    have h1 : |R * Real.cos θ| ≤ |R| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg R) (abs_cos_le_one θ)
    constructor <;> linarith [abs_le.1 h1]
  rw [this, Measure.restrict_apply MeasurableSet.empty, empty_inter, measure_empty, smul_zero]

/-- Integrals against the arcsine measure. -/
lemma integral_arcsineMeasure {f : ℝ → ℝ} (hf : Measurable f) (c R : ℝ) :
    ∫ y, f y ∂arcsineMeasure c R = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f (c + R * Real.cos θ) := by
  rw [arcsineMeasure, integral_smul_measure, integral_map (measurable_arcsineParam c R).aemeasurable
    hf.aestronglyMeasurable, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    intervalIntegral.integral_of_le two_pi_pos.le]

/-- The potential of the arcsine measure as a circle average over the unit circle. -/
lemma logPot_arcsineMeasure_eq_circleAverage (c R : ℝ) (z : ℂ) :
    ∫ y, Real.log ‖z - (y : ℂ)‖ ∂arcsineMeasure c R =
      circleAverage (fun w : ℂ => Real.log ‖z - ((c + R * w.re : ℝ) : ℂ)‖) 0 1 := by
  rw [integral_arcsineMeasure (by fun_prop) c R, circleAverage_def, smul_eq_mul]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.exp_ofReal_mul_I_re]

/-- Joukowski factorization: for `|w| = 1`, `z - (c + R Re w) = -(R/2) w⁻¹ (w - w₁)(w - w₂)` when
`w₁ + w₂ = 2 (z - c)/R` and `w₁ w₂ = 1`. -/
lemma joukowski_factor {c R : ℝ} (hR : R ≠ 0) {z w w₁ w₂ : ℂ} (hw : ‖w‖ = 1)
    (hsum : w₁ + w₂ = 2 * ((z - c) / R)) (hprod : w₁ * w₂ = 1) :
    z - ((c + R * w.re : ℝ) : ℂ) = -((R : ℂ) / 2) * w⁻¹ * ((w - w₁) * (w - w₂)) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw, one_pow, inv_one, Complex.ofReal_one, mul_one]
  have hre : ((w.re : ℝ) : ℂ) = (w + w⁻¹) / 2 := by
    rw [hinv, Complex.re_eq_add_conj]
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  have hexp : (w - w₁) * (w - w₂) = w ^ 2 - (w₁ + w₂) * w + w₁ * w₂ := by ring
  rw [hexp, hsum, hprod]
  push_cast
  rw [hre]
  field_simp
  ring

/-- `|w₁| + |w₂| = |ζ - 1| + |ζ + 1|` for the roots of `w² - 2ζ w + 1`. -/
lemma norm_add_norm_roots {ζ d : ℂ} (hd : d ^ 2 = ζ ^ 2 - 1) :
    ‖ζ + d‖ + ‖ζ - d‖ = ‖ζ - 1‖ + ‖ζ + 1‖ := by
  have hA : ‖ζ + d‖ * ‖ζ - d‖ = 1 := by
    rw [← norm_mul, show (ζ + d) * (ζ - d) = ζ ^ 2 - d ^ 2 by ring, hd]
    simp
  have hB : ‖ζ - 1‖ * ‖ζ + 1‖ = ‖d‖ ^ 2 := by
    rw [← norm_mul, show (ζ - 1) * (ζ + 1) = ζ ^ 2 - 1 by ring, ← hd, norm_pow]
  have hsq1 : ‖ζ + d‖ ^ 2 + ‖ζ - d‖ ^ 2 = 2 * ‖ζ‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
    ring
  have hsq2 : ‖ζ - 1‖ ^ 2 + ‖ζ + 1‖ ^ 2 = 2 * ‖ζ‖ ^ 2 + 2 := by
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub, map_one,
      mul_one]
    ring
  have h : (‖ζ + d‖ + ‖ζ - d‖) ^ 2 = (‖ζ - 1‖ + ‖ζ + 1‖) ^ 2 := by
    nlinarith [hA, hB, hsq1, hsq2]
  have h1 : 0 ≤ ‖ζ + d‖ + ‖ζ - d‖ := by positivity
  have h2 : 0 ≤ ‖ζ - 1‖ + ‖ζ + 1‖ := by positivity
  nlinarith [sq_nonneg (‖ζ + d‖ + ‖ζ - d‖ - (‖ζ - 1‖ + ‖ζ + 1‖)),
    sq_nonneg (‖ζ + d‖ + ‖ζ - d‖ + (‖ζ - 1‖ + ‖ζ + 1‖))]

/-- If `A B > 0` with `A B = 1`, then `log⁺ A + log⁺ B = arcosh ((A + B)/2)`. -/
lemma posLog_add_posLog_eq_arcosh {A B : ℝ} (hA : 0 < A) (hAB : A * B = 1) :
    log⁺ A + log⁺ B = arcosh ((A + B) / 2) := by
  set t := Real.log A with ht
  have hAe : A = exp t := (exp_log hA).symm
  have hBe : B = exp (-t) := by
    rw [exp_neg, ← hAe]
    field_simp
    linarith
  have hcosh : (A + B) / 2 = cosh |t| := by rw [cosh_abs, cosh_eq, ← hAe, ← hBe]
  rw [hcosh, arcosh_cosh (abs_nonneg t), hAe, hBe]
  simp only [posLog_apply, log_exp]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonpos h, max_eq_left h, max_eq_right (by linarith)]
    ring

/-- The argument of `arcosh` in the potential formula. -/
noncomputable def arcsineArg (c R : ℝ) (z : ℂ) : ℝ := (‖(z - c) / R - 1‖ + ‖(z - c) / R + 1‖) / 2

lemma one_le_arcsineArg (c R : ℝ) (z : ℂ) : 1 ≤ arcsineArg c R z := by
  unfold arcsineArg
  have := norm_sub_le ((z - c) / R + 1) ((z - c) / R - 1)
  have h2 : (z - c) / R + 1 - ((z - c) / R - 1) = 2 := by ring
  rw [h2] at this
  norm_num at this
  linarith

/-- The Joukowski splitting of the integrand on the unit circle: with `w₁ w₂ = 1` and `|w₁| + |w₂| = 2 s(z)`,
`log |z - (c + R Re w)| = log (R/2) + log |w - w₁| + log |w - w₂|` off `{w₁, w₂}`. -/
lemma arcsine_split {c R : ℝ} (hR : 0 < R) (z : ℂ) :
    ∃ w₁ w₂ : ℂ, w₁ * w₂ = 1 ∧ ‖w₁‖ + ‖w₂‖ = 2 * arcsineArg c R z ∧
      (fun w : ℂ => Real.log ‖z - ((c + R * w.re : ℝ) : ℂ)‖) =ᶠ[codiscreteWithin (sphere 0 |1|)]
        (fun w => Real.log (R / 2) + (Real.log ‖w - w₁‖ + Real.log ‖w - w₂‖)) := by
  set ζ : ℂ := (z - c) / R with hζ
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (ζ ^ 2 - 1) two_pos
  refine ⟨ζ + d, ζ - d, ?_, ?_, ?_⟩
  · rw [show (ζ + d) * (ζ - d) = ζ ^ 2 - d ^ 2 by ring, hd]; ring
  · rw [norm_add_norm_roots hd]; unfold arcsineArg; rw [← hζ]; ring
  have hsum : (ζ + d) + (ζ - d) = 2 * ((z - c) / R) := by rw [← hζ]; ring
  have hprod : (ζ + d) * (ζ - d) = 1 := by
    rw [show (ζ + d) * (ζ - d) = ζ ^ 2 - d ^ 2 by ring, hd]; ring
  have hfin : {w : ℂ | w ≠ ζ + d ∧ w ≠ ζ - d} ∈ codiscreteWithin (sphere (0 : ℂ) |1|) := by
    apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
    intro x _
    refine ⟨univ, univ_mem, ?_⟩
    apply ((finite_singleton (ζ + d)).insert (ζ - d)).subset
    intro w hw
    simp only [univ_inter, Set.mem_sdiff, mem_ofPred_eq, not_and_or, not_not] at hw
    rcases hw.2 with h | h
    · exact mem_insert_of_mem _ h
    · exact mem_insert_iff.2 (Or.inl h)
  filter_upwards [hfin, self_mem_codiscreteWithin (sphere (0 : ℂ) |1|)] with w hw hws
  have hw1 : ‖w‖ = 1 := by simpa using hws
  rw [joukowski_factor hR.ne' hw1 hsum hprod, norm_mul, norm_mul, norm_neg, norm_inv, hw1, inv_one,
    mul_one, norm_mul, Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    Complex.norm_ofNat]
  rw [Real.log_mul (by positivity) (mul_ne_zero (norm_ne_zero_iff.2 (sub_ne_zero.2 hw.1))
    (norm_ne_zero_iff.2 (sub_ne_zero.2 hw.2))), Real.log_mul (norm_ne_zero_iff.2 (sub_ne_zero.2 hw.1))
    (norm_ne_zero_iff.2 (sub_ne_zero.2 hw.2))]

/-- **Potential of the arcsine measure**: for `R > 0` and `z ∈ ℂ`,
`∫ log |z - y| dω(y) = log (R/2) + arcosh ((|ζ - 1| + |ζ + 1|)/2)`, `ζ = (z - c)/R`. -/
theorem logPot_arcsineMeasure {c R : ℝ} (hR : 0 < R) (z : ℂ) :
    ∫ y, Real.log ‖z - (y : ℂ)‖ ∂arcsineMeasure c R = Real.log (R / 2) + arcosh (arcsineArg c R z) := by
  obtain ⟨w₁, w₂, hprod, hnorm, hcongr⟩ := arcsine_split (c := c) hR z
  have hci1 : CircleIntegrable (fun w => Real.log ‖w - w₁‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm fun _ _ => by fun_prop
  have hci2 : CircleIntegrable (fun w => Real.log ‖w - w₂‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm fun _ _ => by fun_prop
  rw [logPot_arcsineMeasure_eq_circleAverage, circleAverage_congr_codiscreteWithin hcongr one_ne_zero,
    circleAverage_fun_add (circleIntegrable_const _ _ _) (hci1.fun_add hci2), circleAverage_const,
    circleAverage_fun_add hci1 hci2, circleAverage_log_norm_sub_const_eq_posLog,
    circleAverage_log_norm_sub_const_eq_posLog]
  congr 1
  have hA : 0 < ‖w₁‖ := by
    rw [norm_pos_iff]; intro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have hAB : ‖w₁‖ * ‖w₂‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  rw [posLog_add_posLog_eq_arcosh hA hAB, hnorm]
  ring_nf

/-- The logarithmic kernel is integrable against the arcsine measure. -/
lemma integrable_log_norm_sub_arcsineMeasure {c R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) (arcsineMeasure c R) := by
  obtain ⟨w₁, w₂, -, -, hcongr⟩ := arcsine_split (c := c) hR z
  have hci1 : CircleIntegrable (fun w => Real.log ‖w - w₁‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm fun _ _ => by fun_prop
  have hci2 : CircleIntegrable (fun w => Real.log ‖w - w₂‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm fun _ _ => by fun_prop
  have hci : CircleIntegrable (fun w : ℂ => Real.log ‖z - ((c + R * w.re : ℝ) : ℂ)‖) 0 1 :=
    ((circleIntegrable_const _ _ _).fun_add (hci1.fun_add hci2)).congr_codiscreteWithin hcongr.symm
  have hθ : IntegrableOn (fun θ : ℝ => Real.log ‖z - ((c + R * Real.cos θ : ℝ) : ℂ)‖) (Ioc 0 (2 * π)) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hci
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioc
    simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.exp_ofReal_mul_I_re]
  unfold arcsineMeasure
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  rw [integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop))
    (measurable_arcsineParam c R).aemeasurable]
  exact hθ

/-- On the segment `[c - R, c + R]` the potential of the arcsine measure equals `log (R/2)`. -/
theorem logPot_arcsineMeasure_of_mem {c R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Icc (c - R) (c + R)) :
    ∫ y, Real.log ‖(x : ℂ) - (y : ℂ)‖ ∂arcsineMeasure c R = Real.log (R / 2) := by
  rw [logPot_arcsineMeasure hR]
  have harg : arcsineArg c R x = 1 := by
    unfold arcsineArg
    have h1 : (((x : ℂ) - c) / R - 1) = (((x - c) / R - 1 : ℝ) : ℂ) := by push_cast; ring
    have h2 : (((x : ℂ) - c) / R + 1) = (((x - c) / R + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hlo : -1 ≤ (x - c) / R := by rw [le_div_iff₀ hR]; linarith [hx.1]
    have hhi : (x - c) / R ≤ 1 := by rw [div_le_iff₀ hR]; linarith [hx.2]
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    ring
  rw [harg, arcosh_zero, add_zero]

/-- The potential of the arcsine measure is at least `log (R/2)` everywhere. -/
theorem log_le_logPot_arcsineMeasure {c R : ℝ} (hR : 0 < R) (z : ℂ) :
    Real.log (R / 2) ≤ ∫ y, Real.log ‖z - (y : ℂ)‖ ∂arcsineMeasure c R := by
  rw [logPot_arcsineMeasure hR]
  linarith [arcosh_nonneg (one_le_arcsineArg c R z)]

/-- The potential of the arcsine measure is continuous on `ℂ`. -/
theorem continuous_logPot_arcsineMeasure {c R : ℝ} (hR : 0 < R) :
    Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂arcsineMeasure c R := by
  have : (fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂arcsineMeasure c R) =
      fun z => Real.log (R / 2) + arcosh (arcsineArg c R z) := by
    ext z; exact logPot_arcsineMeasure hR z
  rw [this]
  refine continuous_const.add (continuousOn_arcosh.comp_continuous ?_ fun z => one_le_arcsineArg c R z)
  unfold arcsineArg
  fun_prop

end AuxCommon.Energy
