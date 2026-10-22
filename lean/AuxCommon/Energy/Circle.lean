import AuxCommon.Energy.PosDef

/-!
# Circle measures and Jensen's formula for the logarithmic kernel

`circleMeasure c R` is the normalized arc-length measure on the circle `|z - c| = |R|`. With Mathlib's Jensen formula
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog` we get `Λ(σ, σ) = log D - log r` for a circle of radius `r`
and `Λ(σ_c, σ_{c'}) ≤ log D - log |c - c'|` for two circles of radius `r` with distinct centers.
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal

namespace AuxCommon.Energy

/-- The normalized arc-length measure on the circle `|z - c| = |R|`. -/
noncomputable def circleMeasure (c : ℂ) (R : ℝ) : Measure ℂ :=
  ENNReal.ofReal (2 * π)⁻¹ • (volume.restrict (Ioc 0 (2 * π))).map (circleMap c R)

lemma lintegral_circleMeasure {f : ℂ → ℝ≥0∞} (hf : Measurable f) (c : ℂ) (R : ℝ) :
    ∫⁻ z, f z ∂(circleMeasure c R) =
      ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioc 0 (2 * π), f (circleMap c R θ) := by
  rw [circleMeasure, lintegral_smul_measure, lintegral_map hf (measurable_circleMap c R), smul_eq_mul]

instance isProbabilityMeasure_circleMeasure (c : ℂ) (R : ℝ) : IsProbabilityMeasure (circleMeasure c R) := by
  constructor
  rw [circleMeasure, Measure.smul_apply, Measure.map_apply (measurable_circleMap c R) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

lemma circleMeasure_ae_mem (c : ℂ) (R : ℝ) : ∀ᵐ z ∂(circleMeasure c R), z ∈ sphere c |R| := by
  rw [ae_iff, circleMeasure, Measure.smul_apply,
    Measure.map_apply (s := {a | a ∉ sphere c |R|}) (measurable_circleMap c R)
      (by exact isClosed_sphere.measurableSet.compl)]
  have : circleMap c R ⁻¹' {a | a ∉ sphere c |R|} = ∅ := by
    ext θ
    simp
  rw [this, Measure.restrict_apply MeasurableSet.empty, empty_inter, measure_empty, smul_zero]

lemma circleMeasure_singleton (c : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℂ) : circleMeasure c R {z} = 0 := by
  rw [circleMeasure, Measure.smul_apply,
    Measure.map_apply (measurable_circleMap c R) (measurableSet_singleton z),
    Measure.restrict_apply (measurable_circleMap c R (measurableSet_singleton z))]
  have hsub : (circleMap c R ⁻¹' {z} ∩ Ioc 0 (2 * π)).Subsingleton := by
    intro x hx y hy
    have hinj := injOn_circleMap_of_abs_sub_le (c := c) hR (a := 0) (b := 2 * π)
      (by rw [zero_sub, abs_neg, abs_of_pos two_pi_pos])
    rw [uIoc_of_le two_pi_pos.le] at hinj
    exact hinj hx.2 hy.2 (hx.1.trans hy.1.symm)
  rw [hsub.measure_zero, smul_zero]

/-- Lower integral of a nonnegative circle-integrable function against the circle measure = its circle average. -/
lemma lintegral_ofReal_circleMeasure {f : ℂ → ℝ} (hf : Measurable f) {c : ℂ} {R : ℝ}
    (hci : CircleIntegrable f c R) (hpos : ∀ z ∈ sphere c |R|, 0 ≤ f z) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂(circleMeasure c R) = ENNReal.ofReal (circleAverage f c R) := by
  rw [lintegral_circleMeasure hf.ennreal_ofReal, circleAverage_def,
    intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul, ← ofReal_integral_eq_lintegral_ofReal,
    ← ENNReal.ofReal_mul (by positivity)]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hci
  · exact Eventually.of_forall fun θ => hpos _ (circleMap_mem_sphere' c R θ)

lemma Lk_sub_comm (D : ℝ) (a b : ℂ) : Lk D (a - b) = Lk D (b - a) := by
  unfold Lk; rw [norm_sub_rev]

/-- `log ρ ≤ log r + log⁺ (r⁻¹ ρ)` for `ρ, r > 0`. -/
lemma log_le_log_add_posLog {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) : log ρ ≤ log r + log⁺ (r⁻¹ * ρ) := by
  have h : log (r⁻¹ * ρ) = log ρ - log r := by
    rw [log_mul (inv_pos.2 hr).ne' hρ.ne', log_inv]; ring
  have : log (r⁻¹ * ρ) ≤ log⁺ (r⁻¹ * ρ) := le_max_right _ _
  linarith

/-- Jensen's formula for the kernel: `∫ (log D - log |w - p|) dσ_{c,r}(w) = log D - log r - log⁺ (|c - p| / r)`. -/
lemma lintegral_Lk_circleMeasure {D : ℝ} (hD : 1 ≤ D) (p c : ℂ) {r : ℝ} (hr : 0 < r)
    (hsub : ∀ w ∈ sphere c r, ‖w - p‖ ≤ D) :
    ∫⁻ w, ENNReal.ofReal (Lk D (w - p)) ∂(circleMeasure c r) =
      ENNReal.ofReal (log D - (log r + log⁺ (r⁻¹ * ‖c - p‖))) := by
  have hci : CircleIntegrable (fun w => log ‖w - p‖) c r :=
    MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by fun_prop)
  have hfun : (fun w => Lk D (w - p)) = (fun _ => log D) - (fun w => log ‖w - p‖) := by
    ext w; simp [Lk]
  rw [lintegral_ofReal_circleMeasure (f := fun w => Lk D (w - p))
    ((measurable_Lk D).comp (measurable_id.sub_const p))]
  · congr 1
    rw [hfun, circleAverage_sub (circleIntegrable_const _ _ _) hci, circleAverage_const,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
  · rw [hfun]; exact (circleIntegrable_const _ _ _).sub hci
  · intro w hw
    rw [abs_of_pos hr] at hw
    simp only [Lk]
    rcases eq_or_ne w p with rfl | hne
    · simp [log_nonneg hD]
    · have := log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hne)) (hsub w hw)
      linarith

lemma norm_le_of_mem_sphere {D : ℝ} {c w : ℂ} {r : ℝ} (hcr : ‖c‖ + r ≤ D / 2) (hw : w ∈ sphere c r) :
    ‖w‖ ≤ D / 2 := by
  have h1 : ‖w - c‖ = r := mem_sphere_iff_norm.1 hw
  linarith [norm_le_insert' w c]

lemma circleMeasure_ae_norm_le {D : ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : ‖c‖ + r ≤ D / 2) :
    ∀ᵐ z ∂(circleMeasure c r), ‖z‖ ≤ D / 2 := by
  filter_upwards [circleMeasure_ae_mem c r] with z hz
  rw [abs_of_pos hr] at hz
  exact norm_le_of_mem_sphere hcr hz

/-- Self-energy of a circle measure: `Λ(σ, σ) = log D - log r`. -/
lemma Lam_circle_self {D : ℝ} (hD : 1 ≤ D) (c : ℂ) {r : ℝ} (hr : 0 < r) (hcr : ‖c‖ + r ≤ D / 2) :
    Lam D (circleMeasure c r) (circleMeasure c r) = ENNReal.ofReal (log D - log r) := by
  unfold Lam
  have hae := circleMeasure_ae_mem c r
  rw [abs_of_pos hr] at hae
  calc ∫⁻ z, ∫⁻ w, ENNReal.ofReal (Lk D (z - w)) ∂circleMeasure c r ∂circleMeasure c r
      = ∫⁻ z, ENNReal.ofReal (log D - log r) ∂circleMeasure c r := by
        apply lintegral_congr_ae
        filter_upwards [hae] with z hz
        simp_rw [Lk_sub_comm D z]
        have hz' := norm_le_of_mem_sphere hcr hz
        rw [lintegral_Lk_circleMeasure hD z c hr fun w hw => (norm_sub_le w z).trans
          (by linarith [norm_le_of_mem_sphere hcr hw])]
        have : ‖c - z‖ = r := by rw [norm_sub_rev]; exact mem_sphere_iff_norm.1 hz
        rw [this, inv_mul_cancel₀ hr.ne', posLog_one, add_zero]
    _ = ENNReal.ofReal (log D - log r) := by rw [lintegral_const, measure_univ, mul_one]

/-- Mutual energy of two circle measures with distinct centers: `Λ(σ_c, σ_{c'}) ≤ log D - log |c - c'|`. -/
lemma Lam_circle_circle_le {D : ℝ} (hD : 1 ≤ D) {c c' : ℂ} (hcc : c ≠ c') {r : ℝ} (hr : 0 < r)
    (hc : ‖c‖ + r ≤ D / 2) (hc' : ‖c'‖ + r ≤ D / 2) :
    Lam D (circleMeasure c r) (circleMeasure c' r) ≤ ENNReal.ofReal (log D - log ‖c - c'‖) := by
  unfold Lam
  have hae := circleMeasure_ae_mem c r
  rw [abs_of_pos hr] at hae
  have hne : ∀ᵐ z ∂circleMeasure c r, z ≠ c' := by
    rw [ae_iff]
    simpa using circleMeasure_singleton c hr.ne' c'
  have hc'D : ‖c'‖ ≤ D / 2 := by linarith
  calc ∫⁻ z, ∫⁻ w, ENNReal.ofReal (Lk D (z - w)) ∂circleMeasure c' r ∂circleMeasure c r
      ≤ ∫⁻ z, ENNReal.ofReal (Lk D (z - c')) ∂circleMeasure c r := by
        apply lintegral_mono_ae
        filter_upwards [hae, hne] with z hz hzc
        simp_rw [Lk_sub_comm D z]
        have hz' := norm_le_of_mem_sphere hc hz
        rw [lintegral_Lk_circleMeasure hD z c' hr fun w hw => (norm_sub_le w z).trans
          (by linarith [norm_le_of_mem_sphere hc' hw])]
        apply ENNReal.ofReal_le_ofReal
        have hρ : 0 < ‖c' - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc.symm)
        have := log_le_log_add_posLog hr hρ
        simp only [Lk]
        linarith
    _ = ENNReal.ofReal (log D - (log r + log⁺ (r⁻¹ * ‖c - c'‖))) :=
        lintegral_Lk_circleMeasure hD c' c hr fun w hw => (norm_sub_le w c').trans
          (by linarith [norm_le_of_mem_sphere hc hw])
    _ ≤ ENNReal.ofReal (log D - log ‖c - c'‖) := by
        apply ENNReal.ofReal_le_ofReal
        have := log_le_log_add_posLog hr (norm_pos_iff.2 (sub_ne_zero.2 hcc))
        linarith

end AuxCommon.Energy
