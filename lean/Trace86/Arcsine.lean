import AuxCommon.RootSum
import AuxCommon.Energy.Arcsine

/-!
# The arcsine (equilibrium) measure of `[0, 6]`

For the upper bound of the Schur–Siegel–Smyth trace problem (Lemma U1 of the paper): the certificate measure is
`μ = (1 - ε) μ₀ + ε ω`, where `ω` is the arcsine measure of `[0, 6]`. Here `ω = omega06` is the abbreviation of
`AuxCommon.Energy.arcsineMeasure 3 3` (the image of the normalized Lebesgue measure on `(0, 2π]` under
`θ ↦ 3 + 3 cos θ`); equivalently it is the image of `dθ/π` on `[0, π]` under `θ ↦ 3 - 3 cos θ` (`omega06_eq_image`).

* `omega06` is a probability measure carried by `[0, 6]` (`omega06_compl_Icc`), without atoms (`omega06_singleton`),
  with mean `3` (`integral_id_omega06`).
* `logPot_omega06`: `U_ω(z) = ∫ log |z - y| dω(y) = log (3/2) + arcosh ((|z| + |z - 6|)/6)` for every `z ∈ ℂ`. Hence
  `U_ω ≥ log (3/2)` on `ℂ`, `U_ω = log (3/2)` on `[0, 6]` (`3/2` is the capacity of `[0, 6]`), `U_ω` is continuous on
  `ℂ`, and `y ↦ log |z - y|` is `ω`-integrable for every `z` (from `AuxCommon.Energy`).
* For nonzero `Q ∈ ℤ[X]`: `log |Q|` is `ω`-integrable, `∫ log |Q| dω = log |lc Q| + ∑_ρ U_ω(ρ)` over the complex roots,
  `∫ log |Q| dω ≥ log |lc Q| + deg Q · log (3/2)`, with equality when all roots lie in `[0, 6]` (from
  `AuxCommon.RootSum`). Here `(Q.map (Int.castRingHom ℝ)).eval x` is `evalR Q x` and `Q.map (Int.castRingHom ℂ)` is
  `toC Q` of `Trace86.Statement` / `AuxCommon.Basic` (both abbreviations).
-/

open MeasureTheory Set Real Polynomial

namespace Trace86

/-- The arcsine (equilibrium) measure `ω` of `[0, 6]` (`AuxCommon.Energy.arcsineMeasure 3 3`). -/
noncomputable abbrev omega06 : Measure ℝ := AuxCommon.Energy.arcsineMeasure 3 3

/-! ## The image of `dθ/π` on `[0, π]` under `θ ↦ 3 - 3 cos θ` -/

/-- The image of `dθ/π` on `[0, π]` under `θ ↦ 3 - 3 cos θ`. -/
noncomputable def arcsineImage06 : Measure ℝ :=
  ENNReal.ofReal π⁻¹ • (volume.restrict (Icc 0 π)).map (fun θ => 3 - 3 * cos θ)

lemma measurable_arcsineMap06 : Measurable (fun θ : ℝ => 3 - 3 * cos θ) := by fun_prop

instance isProbabilityMeasure_arcsineImage06 : IsProbabilityMeasure arcsineImage06 := by
  constructor
  rw [arcsineImage06, Measure.smul_apply, Measure.map_apply measurable_arcsineMap06 MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc, sub_zero, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ pi_pos.ne', ENNReal.ofReal_one]

lemma arcsineImage06_singleton (x : ℝ) : arcsineImage06 {x} = 0 := by
  rw [arcsineImage06, Measure.smul_apply, Measure.map_apply measurable_arcsineMap06 (measurableSet_singleton x),
    Measure.restrict_apply (measurable_arcsineMap06 (measurableSet_singleton x))]
  have hsub : ((fun θ : ℝ => 3 - 3 * cos θ) ⁻¹' {x} ∩ Icc 0 π).Subsingleton := by
    intro a ha b hb
    apply injOn_cos ha.2 hb.2
    have h1 : 3 - 3 * cos a = x := ha.1
    have h2 : 3 - 3 * cos b = x := hb.1
    linarith
  rw [hsub.measure_zero, smul_zero]

lemma integral_arcsineImage06 {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂arcsineImage06 = π⁻¹ * ∫ θ in Icc 0 π, f (3 - 3 * cos θ) := by
  rw [arcsineImage06, integral_smul_measure,
    integral_map measurable_arcsineMap06.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma integrable_arcsineImage06_iff {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f arcsineImage06 ↔ IntegrableOn (fun θ => f (3 - 3 * cos θ)) (Icc 0 π) := by
  rw [arcsineImage06, integrable_smul_measure (by simp [pi_pos]) ENNReal.ofReal_ne_top,
    integrable_map_measure hf.aestronglyMeasurable measurable_arcsineMap06.aemeasurable]
  rfl

/-- Symmetry `θ ↦ 2π - θ`: `∫_0^{2π} g = 2 ∫_0^π g`. -/
lemma intervalIntegral_zero_two_pi {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 (2 * π))
    (hsym : ∀ θ, g (2 * π - θ) = g θ) : ∫ θ in (0)..(2 * π), g θ = 2 * ∫ θ in (0)..π, g θ := by
  have h1 : IntervalIntegrable g volume 0 π := hg.mono_set (by
    rw [uIcc_of_le pi_pos.le, uIcc_of_le two_pi_pos.le]
    exact Icc_subset_Icc le_rfl (by linarith [pi_pos]))
  have h2 : IntervalIntegrable g volume π (2 * π) := hg.mono_set (by
    rw [uIcc_of_le (by linarith [pi_pos]), uIcc_of_le two_pi_pos.le]
    exact Icc_subset_Icc pi_pos.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have h3 : ∫ θ in π..(2 * π), g θ = ∫ θ in (0)..π, g θ := by
    have := intervalIntegral.integral_comp_sub_left g (2 * π) (a := 0) (b := π)
    simp only [hsym] at this
    rw [this]
    congr 1 <;> ring
  rw [h3]
  ring

/-- `ω` is the image of `dθ/π` on `[0, π]` under `θ ↦ 3 - 3 cos θ`. -/
theorem omega06_eq_image :
    omega06 = ENNReal.ofReal π⁻¹ • (volume.restrict (Icc 0 π)).map (fun θ => 3 - 3 * cos θ) := by
  show AuxCommon.Energy.arcsineMeasure 3 3 = arcsineImage06
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hf : Continuous f := f.continuous
  rw [AuxCommon.Energy.integral_arcsineMeasure hf.measurable, integral_arcsineImage06 hf.measurable,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le pi_pos.le]
  have hg : Continuous fun θ => f (3 + 3 * cos θ) := by fun_prop
  rw [intervalIntegral_zero_two_pi (hg.intervalIntegrable _ _) (fun θ => by rw [cos_two_pi_sub])]
  have h2 : ∫ θ in (0)..π, f (3 + 3 * cos θ) = ∫ θ in (0)..π, f (3 - 3 * cos θ) := by
    have := intervalIntegral.integral_comp_sub_left (fun θ => f (3 + 3 * cos θ)) π (a := 0) (b := π)
    simp only [cos_pi_sub, sub_self, sub_zero] at this
    rw [← this]
    congr 1
    funext θ
    ring_nf
  rw [h2]
  field_simp

lemma omega06_eq_image' : omega06 = arcsineImage06 := omega06_eq_image

/-! ## Basic properties -/

instance isProbabilityMeasure_omega06 : IsProbabilityMeasure omega06 :=
  AuxCommon.Energy.isProbabilityMeasure_arcsineMeasure 3 3

theorem omega06_compl_Icc : omega06 (Icc 0 6)ᶜ = 0 := by
  have h := AuxCommon.Energy.arcsineMeasure_compl_Icc 3 3
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 3), show (3 : ℝ) - 3 = 0 by norm_num,
    show (3 : ℝ) + 3 = 6 by norm_num] at h

theorem omega06_singleton (x : ℝ) : omega06 {x} = 0 := by
  rw [omega06_eq_image']
  exact arcsineImage06_singleton x

instance : NullSingletonClass omega06 := ⟨omega06_singleton⟩

/-- Change of variables: `∫ f dω = (1/π) ∫_{[0, π]} f(3 - 3 cos θ) dθ`. -/
theorem integral_omega06 {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂omega06 = π⁻¹ * ∫ θ in Icc 0 π, f (3 - 3 * cos θ) := by
  rw [omega06_eq_image']
  exact integral_arcsineImage06 hf

theorem integrable_omega06_iff {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f omega06 ↔ IntegrableOn (fun θ => f (3 - 3 * cos θ)) (Icc 0 π) := by
  rw [omega06_eq_image']
  exact integrable_arcsineImage06_iff hf

theorem integral_id_omega06 : ∫ x, x ∂omega06 = 3 := by
  rw [integral_omega06 (f := fun x => x) measurable_id, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le pi_pos.le]
  have : ∫ θ in (0)..π, (3 - 3 * cos θ) = 3 * π := by
    have h2 : IntervalIntegrable (fun θ => 3 * cos θ) volume 0 π :=
      (by fun_prop : Continuous fun θ => 3 * cos θ).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const h2, intervalIntegral.integral_const_mul,
      integral_cos, sin_pi, sin_zero, intervalIntegral.integral_const]
    simp
    ring
  rw [this]
  field_simp

theorem integrable_id_omega06 : Integrable (fun x : ℝ => x) omega06 :=
  AuxCommon.integrable_of_continuous_of_compl_Icc omega06_compl_Icc continuous_id

/-! ## The potential -/

/-- **Potential of the arcsine measure** (closed form): for every `z ∈ ℂ`,
`U_ω(z) = ∫ log |z - y| dω(y) = log (3/2) + arcosh ((|z| + |z - 6|)/6)`. -/
theorem logPot_omega06 (z : ℂ) :
    ∫ y, log ‖z - (y : ℂ)‖ ∂omega06 = log (3 / 2) + arcosh ((‖z‖ + ‖z - 6‖) / 6) := by
  rw [AuxCommon.Energy.logPot_arcsineMeasure (by norm_num : (0 : ℝ) < 3) z]
  congr 2
  unfold AuxCommon.Energy.arcsineArg
  have e1 : (z - ((3 : ℝ) : ℂ)) / ((3 : ℝ) : ℂ) - 1 = (z - 6) / 3 := by push_cast; ring
  have e2 : (z - ((3 : ℝ) : ℂ)) / ((3 : ℝ) : ℂ) + 1 = z / 3 := by push_cast; ring
  rw [e1, e2, norm_div, norm_div, Complex.norm_ofNat]
  ring

theorem log_three_halves_le_logPot_omega06 (z : ℂ) : log (3 / 2) ≤ ∫ y, log ‖z - (y : ℂ)‖ ∂omega06 :=
  AuxCommon.Energy.log_le_logPot_arcsineMeasure (by norm_num) z

/-- `U_ω = log (3/2)` on `[0, 6]` (the capacity of `[0, 6]` is `3/2`). -/
theorem logPot_omega06_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 6) :
    ∫ y, log |x - y| ∂omega06 = log (3 / 2) := by
  have h := AuxCommon.Energy.logPot_arcsineMeasure_of_mem (c := 3) (R := 3) (by norm_num) (x := x)
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have e : ∀ y : ℝ, |x - y| = ‖(x : ℂ) - (y : ℂ)‖ := fun y => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [e]
  exact h

theorem continuous_logPot_omega06 : Continuous fun z : ℂ => ∫ y, log ‖z - (y : ℂ)‖ ∂omega06 :=
  AuxCommon.Energy.continuous_logPot_arcsineMeasure (by norm_num)

theorem integrable_log_omega06 (z : ℂ) : Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) omega06 :=
  AuxCommon.Energy.integrable_log_norm_sub_arcsineMeasure (by norm_num) z

/-! ## Polynomials -/

theorem integrable_log_norm_eval_omega06 {P : ℂ[X]} (hP : P ≠ 0) :
    Integrable (fun x : ℝ => log ‖P.eval (x : ℂ)‖) omega06 :=
  AuxCommon.integrable_log_norm_eval integrable_log_omega06 hP

/-- `∫ log |P| dω = log |lc P| + ∑_ρ U_ω(ρ)` over the complex roots `ρ` of `P` (with multiplicity). -/
theorem integral_log_norm_eval_omega06 {P : ℂ[X]} (hP : P ≠ 0) :
    ∫ x, log ‖P.eval (x : ℂ)‖ ∂omega06 =
      log ‖P.leadingCoeff‖ + (P.roots.map fun ρ => ∫ y, log ‖ρ - (y : ℂ)‖ ∂omega06).sum := by
  rw [AuxCommon.integral_log_norm_eval integrable_log_omega06 hP, probReal_univ, one_mul]

theorem le_integral_log_norm_eval_omega06 {P : ℂ[X]} (hP : P ≠ 0) :
    log ‖P.leadingCoeff‖ + P.natDegree * log (3 / 2) ≤ ∫ x, log ‖P.eval (x : ℂ)‖ ∂omega06 := by
  have h := AuxCommon.le_integral_log_norm_eval integrable_log_omega06 hP
    (fun ρ _ => log_three_halves_le_logPot_omega06 ρ)
  rwa [probReal_univ, one_mul] at h

/-- `log |Q|` is `ω`-integrable for every nonzero `Q ∈ ℤ[X]`. -/
theorem integrable_log_evalR_omega06 {Q : ℤ[X]} (hQ : Q ≠ 0) :
    Integrable (fun x => log |(Q.map (Int.castRingHom ℝ)).eval x|) omega06 :=
  AuxCommon.integrable_log_evalR integrable_log_omega06 hQ

/-- `∫ log |Q| dω = log |lc Q| + ∑_ρ U_ω(ρ)` over the complex roots `ρ` of a nonzero `Q ∈ ℤ[X]`. -/
theorem integral_log_evalR_omega06 {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂omega06 =
      log |(Q.leadingCoeff : ℝ)| +
        ((Q.map (Int.castRingHom ℂ)).roots.map fun ρ => ∫ y, log ‖ρ - (y : ℂ)‖ ∂omega06).sum :=
  AuxCommon.integral_log_evalR integrable_log_omega06 hQ

/-- `∫ log |Q| dω ≥ log |lc Q| + deg Q · log (3/2)` for every nonzero `Q ∈ ℤ[X]`. -/
theorem le_integral_log_evalR_omega06 {Q : ℤ[X]} (hQ : Q ≠ 0) :
    log |(Q.leadingCoeff : ℝ)| + Q.natDegree * log (3 / 2) ≤
      ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂omega06 :=
  AuxCommon.le_integral_log_evalR integrable_log_omega06 hQ fun ρ _ => log_three_halves_le_logPot_omega06 ρ

/-- Equality `∫ log |Q| dω = log |lc Q| + deg Q · log (3/2)` when all complex roots of `Q` lie in `[0, 6]`. -/
theorem integral_log_evalR_omega06_of_roots {Q : ℤ[X]} (hQ : Q ≠ 0)
    (hr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 6) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂omega06 =
      log |(Q.leadingCoeff : ℝ)| + Q.natDegree * log (3 / 2) := by
  refine AuxCommon.integral_log_evalR_of_roots integrable_log_omega06 hQ fun ρ hρ => ?_
  obtain ⟨him, h0, h6⟩ := hr ρ hρ
  have hρ' : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hρ']
  have e : ∀ y : ℝ, ‖(ρ.re : ℂ) - (y : ℂ)‖ = |ρ.re - y| := fun y => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [e]
  exact logPot_omega06_of_mem_Icc ⟨h0, h6⟩

end Trace86
