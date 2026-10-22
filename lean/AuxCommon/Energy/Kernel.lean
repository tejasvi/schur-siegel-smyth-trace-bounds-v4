import Mathlib

/-!
# Kernel identities for the proof of `EnergySmoothing`

* `lintegral_posLog_div_le`: layer-cake bound `∫ log⁺ (r / |a - y|) dν(y) ≤ K r` for a measure with
  `ν(B(y, u)) ≤ K u` (`0 < u ≤ 1`) and `0 < r ≤ 1`.
* `lintegral_frullani`: `∫_0^∞ (e^{-sa} - e^{-sb}) ds / s = log b - log a` for `0 < a ≤ b`.
* `ofReal_Lk_eq`: `log D - log |x| = ∫_0^∞ (e^{-s|x|²} - e^{-sD²}) ds / (2s)` for `x ≠ 0`, both sides clipped at `0`.
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal

namespace AuxCommon.Energy

/-- `log⁺ (r / ρ) ≤ ∫_{(0, r]} 1{ρ < u} du / u`; for `ρ = 0` the left side is `log⁺ 0 = 0`. -/
lemma ofReal_posLog_div_le {r ρ : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (log⁺ (r / ρ)) ≤
      ∫⁻ u in Ioc 0 r, (if ρ < u then ENNReal.ofReal u⁻¹ else 0) := by
  rcases hρ.eq_or_lt with rfl | hρ
  · simp
  rcases le_or_gt r ρ with hrρ | hρr
  · have : log⁺ (r / ρ) = 0 := by
      rw [posLog_eq_zero_iff, abs_of_nonneg (by positivity)]
      exact (div_le_one hρ).2 hrρ
    simp [this]
  have h1 : log⁺ (r / ρ) = log (r / ρ) :=
    posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact (one_le_div hρ).2 hρr.le)
  rw [h1]
  calc ENNReal.ofReal (log (r / ρ)) = ENNReal.ofReal (∫ u in Ioc ρ r, u⁻¹) := by
        rw [← intervalIntegral.integral_of_le hρr.le, integral_inv_of_pos hρ hr]
    _ = ∫⁻ u in Ioc ρ r, ENNReal.ofReal u⁻¹ := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
          exact continuousOn_inv₀.mono fun x hx => (hρ.trans_le hx.1).ne'
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact inv_nonneg.2 (hρ.le.trans hu.1.le)
    _ = ∫⁻ u in Ioc ρ r, (if ρ < u then ENNReal.ofReal u⁻¹ else 0) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
        simp [hu.1]
    _ ≤ ∫⁻ u in Ioc 0 r, (if ρ < u then ENNReal.ofReal u⁻¹ else 0) :=
        lintegral_mono_set (Ioc_subset_Ioc_left hρ.le)

/-- Layer-cake bound: if `ν(B(y, u)) ≤ K u` for `0 < u ≤ 1`, then `∫ log⁺ (r / |a - y|) dν(y) ≤ K r`
for `0 < r ≤ 1`. -/
lemma lintegral_posLog_div_le {ν : Measure ℂ} [IsFiniteMeasure ν] {K : ℝ} (hK : 0 ≤ K)
    (hdisc : ∀ (y : ℂ) (u : ℝ), 0 < u → u ≤ 1 → (ν (ball y u)).toReal ≤ K * u)
    (a : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ y, ENNReal.ofReal (log⁺ (r / ‖a - y‖)) ∂ν ≤ ENNReal.ofReal (K * r) := by
  calc ∫⁻ y, ENNReal.ofReal (log⁺ (r / ‖a - y‖)) ∂ν
      ≤ ∫⁻ y, (∫⁻ u in Ioc 0 r, (if ‖a - y‖ < u then ENNReal.ofReal u⁻¹ else 0)) ∂ν :=
        lintegral_mono fun y => ofReal_posLog_div_le hr (norm_nonneg _)
    _ = ∫⁻ u in Ioc 0 r, ∫⁻ y, (if ‖a - y‖ < u then ENNReal.ofReal u⁻¹ else 0) ∂ν := by
        apply lintegral_lintegral_swap
        refine Measurable.aemeasurable ?_
        refine Measurable.ite ?_ (measurable_snd.inv.ennreal_ofReal) measurable_const
        exact measurableSet_lt (by fun_prop) measurable_snd
    _ = ∫⁻ u in Ioc 0 r, ENNReal.ofReal u⁻¹ * ν (ball a u) := by
        refine lintegral_congr fun u => ?_
        rw [← lintegral_indicator_const measurableSet_ball]
        refine lintegral_congr fun y => ?_
        simp only [indicator, mem_ball, dist_eq_norm, norm_sub_rev y a]
    _ ≤ ∫⁻ u in Ioc 0 r, ENNReal.ofReal K := by
        refine setLIntegral_mono' measurableSet_Ioc fun u hu => ?_
        have hb : ν (ball a u) ≤ ENNReal.ofReal (K * u) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
          exact ENNReal.ofReal_le_ofReal (hdisc a u hu.1 (hu.2.trans hr1))
        calc ENNReal.ofReal u⁻¹ * ν (ball a u)
            ≤ ENNReal.ofReal u⁻¹ * ENNReal.ofReal (K * u) := by gcongr
          _ = ENNReal.ofReal K := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 hu.1.le)]
            congr 1
            field_simp [hu.1.ne']
    _ = ENNReal.ofReal (K * r) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hK]

/-- `∫_a^b e^{-sv} dv = (e^{-sa} - e^{-sb}) / s` for `s ≠ 0`. -/
lemma integral_exp_neg_mul {s : ℝ} (hs : s ≠ 0) (a b : ℝ) :
    ∫ v in a..b, exp (-(s * v)) = (exp (-(s * a)) - exp (-(s * b))) / s := by
  have h := intervalIntegral.integral_comp_mul_left (fun t => exp (-t)) hs (a := a) (b := b)
  rw [h, intervalIntegral.integral_comp_neg (fun t => exp t), integral_exp, smul_eq_mul]
  field_simp

/-- Frullani's integral as a lower Lebesgue integral: `∫_0^∞ (e^{-sa} - e^{-sb}) ds / s = log b - log a`
for `0 < a ≤ b`. -/
lemma lintegral_frullani {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal ((exp (-(s * a)) - exp (-(s * b))) / s) =
      ENNReal.ofReal (log b - log a) := by
  have hb : 0 < b := ha.trans_le hab
  calc ∫⁻ s in Ioi 0, ENNReal.ofReal ((exp (-(s * a)) - exp (-(s * b))) / s)
      = ∫⁻ s in Ioi 0, ∫⁻ v in Ioc a b, ENNReal.ofReal (exp (-(s * v))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [← integral_exp_neg_mul (ne_of_gt hs), intervalIntegral.integral_of_le hab,
          ofReal_integral_eq_lintegral_ofReal]
        · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
        · exact Eventually.of_forall fun v => (exp_pos _).le
    _ = ∫⁻ v in Ioc a b, ∫⁻ s in Ioi 0, ENNReal.ofReal (exp (-(s * v))) := by
        apply lintegral_lintegral_swap
        exact (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable
    _ = ∫⁻ v in Ioc a b, ENNReal.ofReal v⁻¹ := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
        have hv0 : 0 < v := ha.trans hv.1
        have hI : ∫ s in Ioi (0 : ℝ), exp (-(s * v)) = v⁻¹ := by
          have := integral_exp_mul_Ioi (a := -v) (by linarith) 0
          simp only [mul_zero, exp_zero] at this
          rw [show (fun s => exp (-(s * v))) = fun s => exp (-v * s) by ext s; ring_nf, this]
          field_simp
        rw [← hI, ofReal_integral_eq_lintegral_ofReal]
        · exact Integrable.of_integral_ne_zero (by rw [hI]; exact (inv_pos.2 hv0).ne')
        · exact Eventually.of_forall fun s => (exp_pos _).le
    _ = ENNReal.ofReal (log b - log a) := by
        rw [← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le hab,
          integral_inv_of_pos ha hb, log_div hb.ne' ha.ne']
        · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
          exact continuousOn_inv₀.mono fun x hx => (ha.trans_le hx.1).ne'
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact inv_nonneg.2 (ha.le.trans hu.1.le)

/-- The logarithmic kernel `log D - log |x|`; it is `≥ 0` for `0 < |x| ≤ D`. -/
noncomputable def Lk (D : ℝ) (x : ℂ) : ℝ := log D - log ‖x‖

/-- The integrand of the Frullani representation of `Lk D`. -/
noncomputable def gk (D s : ℝ) (x : ℂ) : ℝ := (exp (-(s * ‖x‖ ^ 2)) - exp (-(s * D ^ 2))) / (2 * s)

lemma measurable_gk (D : ℝ) : Measurable fun p : ℝ × ℂ => gk D p.1 p.2 := by
  unfold gk; fun_prop

lemma measurable_Lk (D : ℝ) : Measurable (Lk D) := by
  unfold Lk; fun_prop

/-- Frullani representation of the logarithmic kernel: for `x ≠ 0`,
`(log D - log |x|)⁺ = ∫_0^∞ ((e^{-s|x|²} - e^{-sD²}) / (2s))⁺ ds`. -/
lemma ofReal_Lk_eq {D : ℝ} (hD : 0 < D) {x : ℂ} (hx : x ≠ 0) :
    ENNReal.ofReal (Lk D x) = ∫⁻ s in Ioi 0, ENNReal.ofReal (gk D s x) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rcases le_or_gt ‖x‖ D with hxD | hxD
  · have hab : ‖x‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hx'.le hxD 2
    have key := lintegral_frullani (pow_pos hx' 2) hab
    have e1 : EqOn (fun s => ENNReal.ofReal (gk D s x))
        (fun s => ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal ((exp (-(s * ‖x‖ ^ 2)) - exp (-(s * D ^ 2))) / s)) (Ioi 0) := by
      intro s hs
      simp only
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      unfold gk
      have : s ≠ 0 := ne_of_gt hs
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, key,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    unfold Lk
    rw [Real.log_pow, Real.log_pow]
    push_cast
    ring
  · have h1 : Lk D x ≤ 0 := by
      unfold Lk
      linarith [Real.log_lt_log hD hxD]
    rw [ENNReal.ofReal_of_nonpos h1]
    symm
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) ?_, lintegral_zero]
    intro s hs
    apply ENNReal.ofReal_of_nonpos
    have hs0 : (0 : ℝ) < s := hs
    unfold gk
    apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
    have : s * D ^ 2 < s * ‖x‖ ^ 2 := by
      have : D ^ 2 < ‖x‖ ^ 2 := by gcongr
      exact mul_lt_mul_of_pos_left this hs0
    linarith [exp_lt_exp.2 (neg_lt_neg this)]

end AuxCommon.Energy
