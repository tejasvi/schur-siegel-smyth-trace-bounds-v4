import AuxCommon.Energy.Circle
import AuxCommon.Basic

/-!
# The reference measure: potential, energy, and mutual energy with a circle measure

For a probability measure `ν` with `DiscBound ν K`, a.e. supported in `closedBall 0 (D/2)` (`D ≥ 1`):
* `lintegral_Lk_eq`: `∫ (log D - log |a - y|) dν(y) = log D - U_ν(a)` (no junk value: the integrand is integrable);
* `Lam_nu_nu`: `Λ(ν, ν) = log D - I(ν)`;
* `Lam_circle_nu_add`: `Λ(σ_{c,r}, ν) + ∫ log⁺ (r / |c - y|) dν(y) = log D - U_ν(c)` (smoothing identity).
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal

namespace AuxCommon.Energy

variable {ν : Measure ℂ} [IsProbabilityMeasure ν] {K D : ℝ}

lemma ofReal_Lk_le_add (hD : 1 ≤ D) (x : ℂ) :
    ENNReal.ofReal (Lk D x) ≤ ENNReal.ofReal (log D) + ENNReal.ofReal (log⁺ (1 / ‖x‖)) := by
  rw [← ENNReal.ofReal_add (log_nonneg hD) posLog_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have : -log ‖x‖ ≤ log⁺ (1 / ‖x‖) := by
    rw [one_div, ← log_inv]; exact le_max_right _ _
  simp only [Lk]
  linarith

/-- `∫ (log D - log |a - y|)⁺ dν(y) ≤ log D + K`. -/
lemma lintegral_Lk_le (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (a : ℂ) :
    ∫⁻ y, ENNReal.ofReal (Lk D (a - y)) ∂ν ≤ ENNReal.ofReal (log D + K) := by
  calc ∫⁻ y, ENNReal.ofReal (Lk D (a - y)) ∂ν
      ≤ ∫⁻ y, (ENNReal.ofReal (log D) + ENNReal.ofReal (log⁺ (1 / ‖a - y‖))) ∂ν :=
        lintegral_mono fun y => ofReal_Lk_le_add hD _
    _ = ENNReal.ofReal (log D) + ∫⁻ y, ENNReal.ofReal (log⁺ (1 / ‖a - y‖)) ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (log D) + ENNReal.ofReal (K * 1) := by
        gcongr
        exact lintegral_posLog_div_le hK hdisc a one_pos le_rfl
    _ = ENNReal.ofReal (log D + K) := by rw [mul_one, ENNReal.ofReal_add (log_nonneg hD) hK]

omit [IsProbabilityMeasure ν] in
lemma Lk_nonneg_ae (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2) {a : ℂ} (ha : ‖a‖ ≤ D / 2) :
    ∀ᵐ y ∂ν, 0 ≤ Lk D (a - y) := by
  filter_upwards [hsupp] with y hy
  simp only [Lk]
  rcases eq_or_ne a y with rfl | hne
  · simp [log_nonneg hD]
  · have := log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hne))
      ((norm_sub_le a y).trans (by linarith : ‖a‖ + ‖y‖ ≤ D))
    linarith

lemma integrable_Lk (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2)
    {a : ℂ} (ha : ‖a‖ ≤ D / 2) : Integrable (fun y => Lk D (a - y)) ν := by
  refine ⟨((measurable_Lk D).comp (measurable_const.sub measurable_id)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Lk_nonneg_ae hD hsupp ha)]
  exact (lintegral_Lk_le hK hdisc hD a).trans_lt ENNReal.ofReal_lt_top

lemma integral_Lk_eq (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2)
    {a : ℂ} (ha : ‖a‖ ≤ D / 2) : ∫ y, Lk D (a - y) ∂ν = log D - logPot ν a := by
  have hint : Integrable (fun y => log ‖a - y‖) ν := by
    refine ((integrable_const (log D)).sub (integrable_Lk hK hdisc hD hsupp ha)).congr
      (Eventually.of_forall fun y => ?_)
    simp [Lk]
  simp only [Lk, logPot]
  rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul]

/-- `∫ (log D - log |a - y|) dν(y) = log D - U_ν(a)`, as a lower integral. -/
lemma lintegral_Lk_eq (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2)
    {a : ℂ} (ha : ‖a‖ ≤ D / 2) :
    ∫⁻ y, ENNReal.ofReal (Lk D (a - y)) ∂ν = ENNReal.ofReal (log D - logPot ν a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_Lk hK hdisc hD hsupp ha) (Lk_nonneg_ae hD hsupp ha),
    integral_Lk_eq hK hdisc hD hsupp ha]

/-- `-K ≤ U_ν(a) ≤ log D` on the support. -/
lemma logPot_bounds (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2)
    {a : ℂ} (ha : ‖a‖ ≤ D / 2) : -K ≤ logPot ν a ∧ logPot ν a ≤ log D := by
  have h2 := lintegral_Lk_le hK hdisc hD a
  rw [lintegral_Lk_eq hK hdisc hD hsupp ha] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by linarith [log_nonneg hD])).1 h2
  have h4 : 0 ≤ log D - logPot ν a := by
    rw [← integral_Lk_eq hK hdisc hD hsupp ha]
    exact integral_nonneg_of_ae (Lk_nonneg_ae hD hsupp ha)
  constructor <;> linarith

lemma integrable_logPot (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D)
    (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2) : Integrable (logPot ν) ν := by
  have hmeas : AEStronglyMeasurable (logPot ν) ν := by
    have : StronglyMeasurable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) := by
      apply Measurable.stronglyMeasurable; fun_prop
    exact (this.integral_prod_right' (ν := ν)).aestronglyMeasurable
  refine Integrable.of_bound hmeas (|log D| + K) ?_
  filter_upwards [hsupp] with z hz
  obtain ⟨h1, h2⟩ := logPot_bounds hK hdisc hD hsupp hz
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [le_abs_self (log D), neg_abs_le (log D)]

/-- `I(ν) ≤ log D`. -/
lemma logEnergy_le (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2) :
    logEnergy ν ≤ log D := by
  have h : ∀ᵐ z ∂ν, logPot ν z ≤ log D := by
    filter_upwards [hsupp] with z hz
    exact (logPot_bounds hK hdisc hD hsupp hz).2
  calc logEnergy ν = ∫ z, logPot ν z ∂ν := rfl
    _ ≤ ∫ _z, log D ∂ν := integral_mono_ae (integrable_logPot hK hdisc hD hsupp) (integrable_const _) h
    _ = log D := by rw [integral_const, probReal_univ, one_smul]

/-- `Λ(ν, ν) = log D - I(ν)`. -/
lemma Lam_nu_nu (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2) :
    Lam D ν ν = ENNReal.ofReal (log D - logEnergy ν) := by
  unfold Lam
  have h1 : ∫⁻ z, ∫⁻ y, ENNReal.ofReal (Lk D (z - y)) ∂ν ∂ν =
      ∫⁻ z, ENNReal.ofReal (log D - logPot ν z) ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hsupp] with z hz
    exact lintegral_Lk_eq hK hdisc hD hsupp hz
  have hint2 := integrable_logPot hK hdisc hD hsupp
  have hnn : 0 ≤ᵐ[ν] fun z => log D - logPot ν z := by
    filter_upwards [hsupp] with z hz
    show (0 : ℝ) ≤ log D - logPot ν z
    linarith [(logPot_bounds hK hdisc hD hsupp hz).2]
  have hint : Integrable (fun z => log D - logPot ν z) ν := (integrable_const (log D)).sub hint2
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_sub (integrable_const _) hint2, integral_const, probReal_univ, one_smul]
  rfl

/-- `log r + log⁺ (r⁻¹ ρ) = log ρ + log⁺ (r / ρ)` for `r, ρ > 0` (both are `log max(r, ρ)`). -/
lemma log_add_posLog_eq {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    log r + log⁺ (r⁻¹ * ρ) = log ρ + log⁺ (r / ρ) := by
  rcases le_total ρ r with h | h
  · have h1 : log⁺ (r⁻¹ * ρ) = 0 := by
      rw [posLog_eq_zero_iff, abs_of_nonneg (by positivity), inv_mul_le_iff₀ hr]
      linarith
    have h2 : log⁺ (r / ρ) = log (r / ρ) :=
      posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact (one_le_div hρ).2 h)
    rw [h1, h2, log_div hr.ne' hρ.ne']
    ring
  · have h1 : log⁺ (r⁻¹ * ρ) = log (r⁻¹ * ρ) :=
      posLog_eq_log (by rw [abs_of_pos (by positivity), le_inv_mul_iff₀ hr]; linarith)
    have h2 : log⁺ (r / ρ) = 0 := by
      rw [posLog_eq_zero_iff, abs_of_nonneg (by positivity)]
      exact (div_le_one hρ).2 h
    rw [h1, h2, log_mul (inv_pos.2 hr).ne' hρ.ne', log_inv]
    ring

/-- `log r + log⁺ (r⁻¹ ρ) ≤ log D` for `0 < r ≤ 1 ≤ D` and `0 < ρ ≤ D`. -/
lemma log_add_posLog_le {r ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hρ : 0 < ρ) (hρD : ρ ≤ D) (hD : 1 ≤ D) :
    log r + log⁺ (r⁻¹ * ρ) ≤ log D := by
  rcases le_total (r⁻¹ * ρ) 1 with h | h
  · have h1 : log⁺ (r⁻¹ * ρ) = 0 := by
      rw [posLog_eq_zero_iff, abs_of_nonneg (by positivity)]
      exact h
    rw [h1, add_zero]
    linarith [log_nonpos hr.le hr1, log_nonneg hD]
  · have h1 : log⁺ (r⁻¹ * ρ) = log (r⁻¹ * ρ) := posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact h)
    rw [h1, log_mul (inv_pos.2 hr).ne' hρ.ne', log_inv]
    linarith [log_le_log hρ hρD]

/-- Smoothing identity: `Λ(σ_{c,r}, ν) + ∫ log⁺ (r / |c - y|) dν(y) = log D - U_ν(c)`. -/
lemma Lam_circle_nu_add (hK : 0 ≤ K) (hdisc : DiscBound ν K) (hD : 1 ≤ D) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2)
    (hat : ∀ z, ν {z} = 0) {c : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hcr : ‖c‖ + r ≤ D / 2) :
    Lam D (circleMeasure c r) ν + ∫⁻ y, ENNReal.ofReal (log⁺ (r / ‖c - y‖)) ∂ν =
      ENNReal.ofReal (log D - logPot ν c) := by
  have hc : ‖c‖ ≤ D / 2 := by linarith
  have hswap : Lam D (circleMeasure c r) ν =
      ∫⁻ y, ∫⁻ z, ENNReal.ofReal (Lk D (z - y)) ∂circleMeasure c r ∂ν := by
    unfold Lam
    apply lintegral_lintegral_swap
    unfold Lk
    fun_prop
  have hne : ∀ᵐ y ∂ν, y ≠ c := by
    rw [ae_iff]
    simpa using hat c
  have hg : Measurable fun y : ℂ => ENNReal.ofReal (log⁺ (r / ‖c - y‖)) := by fun_prop
  rw [hswap, ← lintegral_Lk_eq hK hdisc hD hsupp hc, ← lintegral_add_right _ hg]
  apply lintegral_congr_ae
  filter_upwards [hsupp, hne] with y hy hyc
  rw [lintegral_Lk_circleMeasure hD y c hr fun w hw => (norm_sub_le w y).trans
    (by linarith [norm_le_of_mem_sphere hcr hw])]
  have hρ : 0 < ‖c - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hyc.symm)
  have hρD : ‖c - y‖ ≤ D := (norm_sub_le c y).trans (by linarith)
  have hX : 0 ≤ log D - (log r + log⁺ (r⁻¹ * ‖c - y‖)) := by
    linarith [log_add_posLog_le hr hr1 hρ hρD hD]
  rw [← ENNReal.ofReal_add hX posLog_nonneg]
  congr 1
  simp only [Lk]
  rw [log_add_posLog_eq hr hρ]
  ring

end AuxCommon.Energy
