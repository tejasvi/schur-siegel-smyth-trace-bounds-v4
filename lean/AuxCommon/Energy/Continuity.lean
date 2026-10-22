import AuxCommon.Energy.Kernel

/-!
# Continuity of the logarithmic potential of a measure on `ℝ` with a Hölder bound on intervals

`continuous_logPot_of_ball_le`: if `μ` is a finite measure on `ℝ` supported in `[a, b]` with
`μ(x - s, x + s) ≤ K s^γ` for all `x` and `0 < s ≤ 1` (some `γ > 0`), then `z ↦ ∫ log |z - y| dμ(y)` is continuous on
`ℂ` (the continuity hypothesis of `MinPrinciple`). A bounded density `G dx` satisfies the bound with `γ = 1`.

Proof: the truncations `U_M(z) = ∫ log max(|z - y|, e^{-M}) dμ(y)` are continuous (dominated convergence), and
`0 ≤ U_M - U ≤ ∫ log⁺ (e^{-M}/|z - y|) dμ(y) ≤ K e^{-γM}/γ` uniformly in `z` (layer cake), so `U_M → U` uniformly.
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal Topology

namespace AuxCommon.Energy

variable {μ : Measure ℝ}

/-- Layer cake: `∫ log⁺ (ρ / |z - y|) dμ(y) ≤ K ρ^γ / γ` under `μ(x - s, x + s) ≤ K s^γ` (`0 < s ≤ 1`). -/
lemma lintegral_posLog_div_le_rpow [IsFiniteMeasure μ] {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    (hball : ∀ (x s : ℝ), 0 < s → s ≤ 1 → (μ (Ioo (x - s) (x + s))).toReal ≤ K * s ^ γ)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ y, ENNReal.ofReal (log⁺ (ρ / ‖z - (y : ℂ)‖)) ∂μ ≤ ENNReal.ofReal (K * ρ ^ γ / γ) := by
  calc ∫⁻ y, ENNReal.ofReal (log⁺ (ρ / ‖z - (y : ℂ)‖)) ∂μ
      ≤ ∫⁻ y, (∫⁻ s in Ioc 0 ρ, (if ‖z - (y : ℂ)‖ < s then ENNReal.ofReal s⁻¹ else 0)) ∂μ :=
        lintegral_mono fun y => ofReal_posLog_div_le hρ (norm_nonneg _)
    _ = ∫⁻ s in Ioc 0 ρ, ∫⁻ y, (if ‖z - (y : ℂ)‖ < s then ENNReal.ofReal s⁻¹ else 0) ∂μ := by
        apply lintegral_lintegral_swap
        refine Measurable.aemeasurable ?_
        refine Measurable.ite ?_ (measurable_snd.inv.ennreal_ofReal) measurable_const
        exact measurableSet_lt (by fun_prop) measurable_snd
    _ ≤ ∫⁻ s in Ioc 0 ρ, ENNReal.ofReal (K * s ^ (γ - 1)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        have hmeas : MeasurableSet {y : ℝ | ‖z - (y : ℂ)‖ < s} := measurableSet_lt (by fun_prop) measurable_const
        have hsub : {y : ℝ | ‖z - (y : ℂ)‖ < s} ⊆ Ioo (z.re - s) (z.re + s) := by
          intro y hy
          have h1 : |z.re - y| ≤ ‖z - (y : ℂ)‖ := by
            simpa using Complex.abs_re_le_norm (z - (y : ℂ))
          have h2 := abs_lt.1 (h1.trans_lt hy)
          constructor <;> linarith [h2.1, h2.2]
        have hb : μ (Ioo (z.re - s) (z.re + s)) ≤ ENNReal.ofReal (K * s ^ γ) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal (hball z.re s hs.1 (hs.2.trans hρ1))
        calc ∫⁻ y, (if ‖z - (y : ℂ)‖ < s then ENNReal.ofReal s⁻¹ else 0) ∂μ
            = ∫⁻ y, {y : ℝ | ‖z - (y : ℂ)‖ < s}.indicator (fun _ => ENNReal.ofReal s⁻¹) y ∂μ := by
              refine lintegral_congr fun y => ?_
              simp only [indicator, mem_ofPred_eq]
          _ = ENNReal.ofReal s⁻¹ * μ {y : ℝ | ‖z - (y : ℂ)‖ < s} := lintegral_indicator_const hmeas _
          _ ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal (K * s ^ γ) := by
              gcongr
              exact (measure_mono hsub).trans hb
          _ = ENNReal.ofReal (K * s ^ (γ - 1)) := by
              rw [← ENNReal.ofReal_mul (inv_nonneg.2 hs.1.le)]
              congr 1
              rw [rpow_sub hs.1, rpow_one]
              field_simp
    _ = ENNReal.ofReal (K * ρ ^ γ / γ) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          rw [← intervalIntegral.integral_of_le hρ.le, intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (by linarith)), sub_add_cancel, zero_rpow hγ.ne', sub_zero]
          field_simp
        · exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul K).1
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact mul_nonneg hK (rpow_nonneg hs.1.le _)

/-- `|log t| ≤ log⁺ (1/t) + max 0 (log C)` for `0 ≤ t ≤ C`. -/
lemma abs_log_le_posLog_inv_add {t C : ℝ} (ht : 0 ≤ t) (htC : t ≤ C) :
    |log t| ≤ log⁺ (1 / t) + max 0 (log C) := by
  rcases ht.eq_or_lt with rfl | ht0
  · simp only [log_zero, abs_zero]
    exact add_nonneg posLog_nonneg (le_max_left _ _)
  rcases le_or_gt 1 t with h1 | h1
  · rw [abs_of_nonneg (log_nonneg h1)]
    have : log t ≤ log C := log_le_log ht0 htC
    have : 0 ≤ log⁺ (1 / t) := posLog_nonneg
    linarith [le_max_right 0 (log C)]
  · rw [abs_of_neg (log_neg ht0 h1)]
    have : -log t = log (1 / t) := by rw [one_div, log_inv]
    have : log (1 / t) ≤ log⁺ (1 / t) := le_max_right _ _
    linarith [le_max_left 0 (log C)]

/-- Under the interval bound, `y ↦ log |z - y|` is `μ`-integrable for every `z ∈ ℂ`. -/
lemma integrable_log_norm_sub_of_ball_le [IsFiniteMeasure μ] {a b K γ : ℝ} (hsupp : μ (Icc a b)ᶜ = 0)
    (hK : 0 ≤ K) (hγ : 0 < γ)
    (hball : ∀ (x s : ℝ), 0 < s → s ≤ 1 → (μ (Ioo (x - s) (x + s))).toReal ≤ K * s ^ γ) (z : ℂ) :
    Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) μ := by
  set R0 := |a| + |b| with hR0
  have hae : ∀ᵐ y ∂μ, y ∈ Icc a b := by rw [ae_iff]; exact hsupp
  have hyR : ∀ y ∈ Icc a b, |y| ≤ R0 := fun y hy => by
    have := abs_le_max_abs_abs hy.1 hy.2
    linarith [max_le_add_of_nonneg (abs_nonneg a) (abs_nonneg b)]
  refine ⟨Measurable.aestronglyMeasurable (by fun_prop), ?_⟩
  rw [hasFiniteIntegral_def]
  calc ∫⁻ y, ‖Real.log ‖z - (y : ℂ)‖‖ₑ ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal (log⁺ (1 / ‖z - (y : ℂ)‖)) + ENNReal.ofReal (max 0 (log (‖z‖ + R0)))) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hae] with y hy
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add posLog_nonneg (le_max_left _ _)]
        apply ENNReal.ofReal_le_ofReal
        apply abs_log_le_posLog_inv_add (norm_nonneg _)
        have := norm_sub_le z (y : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at this
        linarith [hyR y hy]
    _ = ∫⁻ y, ENNReal.ofReal (log⁺ (1 / ‖z - (y : ℂ)‖)) ∂μ +
          ENNReal.ofReal (max 0 (log (‖z‖ + R0))) * μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)⟩
        exact (lintegral_posLog_div_le_rpow hK hγ hball z one_pos le_rfl).trans_lt ENNReal.ofReal_lt_top

/-- **Continuity of the logarithmic potential** of a finite measure on `ℝ` supported in `[a, b]` with
`μ(x - s, x + s) ≤ K s^γ` (`0 < s ≤ 1`, `γ > 0`). -/
theorem continuous_logPot_of_ball_le [IsFiniteMeasure μ] {a b K γ : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hball : ∀ (x s : ℝ), 0 < s → s ≤ 1 → (μ (Ioo (x - s) (x + s))).toReal ≤ K * s ^ γ) :
    Continuous (fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ) := by
  set R0 := |a| + |b| with hR0
  have hae : ∀ᵐ y ∂μ, y ∈ Icc a b := by rw [ae_iff]; exact hsupp
  have hyR : ∀ y ∈ Icc a b, |y| ≤ R0 := fun y hy => by
    have := abs_le_max_abs_abs hy.1 hy.2
    linarith [max_le_add_of_nonneg (abs_nonneg a) (abs_nonneg b)]
  -- no atoms
  have hatom : ∀ x : ℝ, μ {x} = 0 := by
    intro x
    have h : ∀ s : ℝ, 0 < s → s ≤ 1 → (μ {x}).toReal ≤ K * s ^ γ := fun s hs hs1 =>
      (ENNReal.toReal_mono (measure_ne_top μ _)
        (measure_mono (singleton_subset_iff.2
          (show x ∈ Ioo (x - s) (x + s) from ⟨by linarith, by linarith⟩)))).trans (hball x s hs hs1)
    have h0 : (μ {x}).toReal ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      -- choose s small with K s^γ ≤ ε
      have htend : Tendsto (fun s : ℝ => K * s ^ γ) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun s : ℝ => s ^ γ) (𝓝[>] 0) (𝓝 0) := by
          have := (continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto
          rw [zero_rpow hγ.ne'] at this
          exact this.mono_left nhdsWithin_le_nhds
        simpa using this.const_mul K
      obtain ⟨s, hs, hsε⟩ := ((htend.eventually (gt_mem_nhds hε)).and
        (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
      linarith [h s hsε.1 hsε.2]
    rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
    · exact h
    · exact absurd h (measure_ne_top μ _)
  have hint : ∀ z : ℂ, Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) μ :=
    integrable_log_norm_sub_of_ball_le hsupp hK hγ hball
  set UM : ℕ → ℂ → ℝ := fun M z => ∫ y, Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) ∂μ with hUM
  -- the truncations are continuous
  have hcont : ∀ M : ℕ, Continuous (UM M) := by
    intro M
    rw [continuous_iff_continuousAt]
    intro z0
    refine continuousAt_of_dominated (bound := fun _ => (M : ℝ) + |log (‖z0‖ + 2 + R0)|) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun z => Measurable.aestronglyMeasurable (by fun_prop)
    · filter_upwards [Metric.ball_mem_nhds z0 one_pos] with z hz
      filter_upwards [hae] with y hy
      have hzz : ‖z‖ ≤ ‖z0‖ + 1 := by
        have := norm_le_insert' z z0
        rw [mem_ball, dist_eq_norm] at hz
        linarith
      have hupper : ‖z - (y : ℂ)‖ ≤ ‖z0‖ + 1 + R0 := by
        have := norm_sub_le z (y : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at this
        linarith [hyR y hy]
      have he : exp (-(M : ℝ)) ≤ 1 := exp_le_one_iff.2 (by simp)
      have hmax_pos : 0 < max ‖z - (y : ℂ)‖ (exp (-(M : ℝ))) := lt_max_of_lt_right (exp_pos _)
      have hlow : -(M : ℝ) ≤ Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) := by
        have := log_le_log (exp_pos (-(M : ℝ))) (le_max_right ‖z - (y : ℂ)‖ (exp (-(M : ℝ))))
        rwa [log_exp] at this
      have hup : Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) ≤ log (‖z0‖ + 2 + R0) := by
        apply log_le_log hmax_pos
        apply max_le <;> linarith [norm_nonneg z0, abs_nonneg a, abs_nonneg b]
      have hR : 0 ≤ R0 := by positivity
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [abs_nonneg (log (‖z0‖ + 2 + R0))]
      · linarith [le_abs_self (log (‖z0‖ + 2 + R0)), (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    · refine Eventually.of_forall fun y => ?_
      have h1 : ContinuousAt (fun z : ℂ => max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) z0 := by fun_prop
      exact h1.log (lt_max_of_lt_right (exp_pos _)).ne'
  -- uniform convergence
  have hdiff : ∀ (M : ℕ) (z : ℂ), |UM M z - ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ| ≤
      K * exp (-(M : ℝ)) ^ γ / γ := by
    intro M z
    have hne : ∀ᵐ (y : ℝ) ∂μ, (y : ℂ) ≠ z := by
      rw [ae_iff]
      refine measure_mono_null (t := {z.re}) ?_ (hatom z.re)
      intro y hy
      simp only [mem_ofPred_eq, not_not] at hy
      rw [mem_singleton_iff, ← hy, Complex.ofReal_re]
    have hintM : Integrable (fun y : ℝ => Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ))))) μ := by
      refine Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop))
        ((M : ℝ) + |log (‖z‖ + 1 + R0)|) ?_
      filter_upwards [hae] with y hy
      have hupper : ‖z - (y : ℂ)‖ ≤ ‖z‖ + R0 := by
        have := norm_sub_le z (y : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at this
        linarith [hyR y hy]
      have he : exp (-(M : ℝ)) ≤ 1 := exp_le_one_iff.2 (by simp)
      have hmax_pos : 0 < max ‖z - (y : ℂ)‖ (exp (-(M : ℝ))) := lt_max_of_lt_right (exp_pos _)
      have hlow : -(M : ℝ) ≤ Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) := by
        have := log_le_log (exp_pos (-(M : ℝ))) (le_max_right ‖z - (y : ℂ)‖ (exp (-(M : ℝ))))
        rwa [log_exp] at this
      have hup : Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) ≤ log (‖z‖ + 1 + R0) := by
        apply log_le_log hmax_pos
        apply max_le <;> linarith [norm_nonneg z, abs_nonneg a, abs_nonneg b]
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [abs_nonneg (log (‖z‖ + 1 + R0))]
      · linarith [le_abs_self (log (‖z‖ + 1 + R0)), (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    -- the difference is `∫ log⁺ (e^{-M}/|z - y|)`
    have hpt : ∀ᵐ (y : ℝ) ∂μ, Real.log (max ‖z - (y : ℂ)‖ (exp (-(M : ℝ)))) - Real.log ‖z - (y : ℂ)‖ =
        log⁺ (exp (-(M : ℝ)) / ‖z - (y : ℂ)‖) := by
      filter_upwards [hne] with y hy
      have ht : 0 < ‖z - (y : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 hy.symm)
      rcases le_total (exp (-(M : ℝ))) ‖z - (y : ℂ)‖ with h | h
      · rw [max_eq_left h, sub_self, eq_comm, posLog_eq_zero_iff, abs_of_nonneg (by positivity)]
        exact (div_le_one ht).2 h
      · rw [max_eq_right h, posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact (one_le_div ht).2 h),
          log_div (exp_pos _).ne' ht.ne']
    have hEq : UM M z - ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ = ∫ y, log⁺ (exp (-(M : ℝ)) / ‖z - (y : ℂ)‖) ∂μ := by
      rw [hUM, ← integral_sub hintM (hint z)]
      exact integral_congr_ae hpt
    rw [hEq, abs_of_nonneg (integral_nonneg fun y => posLog_nonneg)]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => posLog_nonneg)
      (Measurable.aestronglyMeasurable (by fun_prop))]
    have hb := lintegral_posLog_div_le_rpow hK hγ hball z (exp_pos (-(M : ℝ)))
      (exp_le_one_iff.2 (by simp))
    calc (∫⁻ y, ENNReal.ofReal (log⁺ (exp (-(M : ℝ)) / ‖z - (y : ℂ)‖)) ∂μ).toReal
        ≤ (ENNReal.ofReal (K * exp (-(M : ℝ)) ^ γ / γ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = K * exp (-(M : ℝ)) ^ γ / γ := ENNReal.toReal_ofReal (by positivity)
  have hunif : TendstoUniformly UM (fun z => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have htend : Tendsto (fun M : ℕ => K * exp (-(M : ℝ)) ^ γ / γ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun M : ℕ => exp (-(M : ℝ))) atTop (𝓝 0) :=
        tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      have h2 : Tendsto (fun M : ℕ => exp (-(M : ℝ)) ^ γ) atTop (𝓝 0) := by
        have := (continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp h1
        rwa [zero_rpow hγ.ne'] at this
      simpa using (h2.const_mul K).div_const γ
    filter_upwards [htend.eventually (gt_mem_nhds hε)] with M hM z
    rw [dist_comm, Real.dist_eq]
    exact (hdiff M z).trans_lt hM
  exact hunif.continuous (Frequently.of_forall hcont)

end AuxCommon.Energy
