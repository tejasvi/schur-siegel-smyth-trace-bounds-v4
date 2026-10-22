import AuxCommon.Energy.Gauss

/-!
# Negativity of the logarithmic energy of mass-zero differences (Saff-Totik, Lemma I.1.8)

For probability measures `μ₁, μ₂` on `ℂ` without atoms, a.e. supported in `closedBall 0 (D/2)`,
`2 Λ(μ₁, μ₂) ≤ Λ(μ₁, μ₁) + Λ(μ₂, μ₂)` where `Λ(μ, μ') = ∫∫ (log D - log |z - w|) dμ'(w) dμ(z)` (lower Lebesgue
integrals, so no finiteness assumption is needed). Proof: Frullani representation of the kernel (`ofReal_Lk_eq`) and
positive definiteness of the Gaussian kernel (`two_mul_gaussForm_le`).
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal

namespace AuxCommon.Energy

/-- `Λ_D(μ, μ') = ∫∫ (log D - log |z - w|)⁺ dμ'(w) dμ(z)`. -/
noncomputable def Lam (D : ℝ) (μ μ' : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ∫⁻ w, ENNReal.ofReal (Lk D (z - w)) ∂μ' ∂μ

/-- The `s`-slice of the Frullani representation of `Λ_D`. -/
noncomputable def Gam (D s : ℝ) (μ μ' : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ∫⁻ w, ENNReal.ofReal (gk D s (z - w)) ∂μ' ∂μ

lemma measurable_Gam (D : ℝ) (μ μ' : Measure ℂ) [SFinite μ] [SFinite μ'] :
    Measurable fun s => Gam D s μ μ' := by
  have h1 : Measurable fun p : (ℝ × ℂ) × ℂ => ENNReal.ofReal (gk D p.1.1 (p.1.2 - p.2)) := by
    unfold gk; fun_prop
  exact (h1.lintegral_prod_right' (ν := μ')).lintegral_prod_right' (ν := μ)

/-- For an atomless `μ'`, `Λ_D(μ, μ') = ∫_0^∞ Γ_s(μ, μ') ds`. -/
lemma Lam_eq_lintegral_Gam {D : ℝ} (hD : 0 < D) (μ μ' : Measure ℂ) [SFinite μ] [SFinite μ']
    (hμ' : ∀ z, μ' {z} = 0) :
    Lam D μ μ' = ∫⁻ s in Ioi 0, Gam D s μ μ' := by
  unfold Lam Gam
  have h1 : ∀ z, ∫⁻ w, ENNReal.ofReal (Lk D (z - w)) ∂μ' =
      ∫⁻ w, (∫⁻ s in Ioi 0, ENNReal.ofReal (gk D s (z - w))) ∂μ' := by
    intro z
    apply lintegral_congr_ae
    have : ∀ᵐ w ∂μ', w ≠ z := by
      rw [ae_iff]
      simpa using hμ' z
    filter_upwards [this] with w hw
    exact ofReal_Lk_eq hD (sub_ne_zero.2 hw.symm)
  simp_rw [h1]
  have h2 : Measurable fun p : (ℂ × ℝ) × ℂ => ENNReal.ofReal (gk D p.1.2 (p.1.1 - p.2)) := by
    unfold gk; fun_prop
  calc ∫⁻ z, ∫⁻ w, (∫⁻ s in Ioi 0, ENNReal.ofReal (gk D s (z - w))) ∂μ' ∂μ
      = ∫⁻ z, (∫⁻ s in Ioi 0, ∫⁻ w, ENNReal.ofReal (gk D s (z - w)) ∂μ') ∂μ := by
        refine lintegral_congr fun z => ?_
        apply lintegral_lintegral_swap
        unfold gk
        fun_prop
    _ = ∫⁻ s in Ioi 0, ∫⁻ z, ∫⁻ w, ENNReal.ofReal (gk D s (z - w)) ∂μ' ∂μ := by
        apply lintegral_lintegral_swap
        exact (h2.lintegral_prod_right' (ν := μ')).aemeasurable

/-- On supports of diameter `≤ D`, `Γ_s(μ, μ') + e^{-sD²}/(2s) = G_s(μ, μ')/(2s)` for probability measures. -/
lemma Gam_add_const {D s : ℝ} (hs : 0 < s) (μ μ' : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (h : ∀ᵐ z ∂μ, ‖z‖ ≤ D / 2) (h' : ∀ᵐ z ∂μ', ‖z‖ ≤ D / 2) :
    Gam D s μ μ' + ENNReal.ofReal (exp (-(s * D ^ 2)) / (2 * s)) =
      ENNReal.ofReal (1 / (2 * s)) * gaussForm s μ μ' := by
  unfold Gam gaussForm
  set c := ENNReal.ofReal (exp (-(s * D ^ 2)) / (2 * s))
  have hm : ∀ z : ℂ, Measurable fun w : ℂ => ENNReal.ofReal (gk D s (z - w)) := by
    intro z; unfold gk; fun_prop
  have hL : ∫⁻ z, ∫⁻ w, ENNReal.ofReal (gk D s (z - w)) ∂μ' ∂μ + c =
      ∫⁻ z, ∫⁻ w, (ENNReal.ofReal (gk D s (z - w)) + c) ∂μ' ∂μ := by
    simp_rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  rw [hL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [h] with z hz
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [h'] with w hw
  have hzw : ‖z - w‖ ≤ D := (norm_sub_le z w).trans (by linarith)
  have hexp : exp (-(s * D ^ 2)) ≤ exp (-(s * ‖z - w‖ ^ 2)) := by
    apply exp_le_exp.2
    have : ‖z - w‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzw 2
    nlinarith
  have hgk : 0 ≤ gk D s (z - w) := by
    unfold gk
    exact div_nonneg (by linarith) (by linarith)
  rw [← ENNReal.ofReal_add hgk (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold gk
  field_simp
  ring

/-- Slice inequality: `2 Γ_s(μ₁, μ₂) ≤ Γ_s(μ₁, μ₁) + Γ_s(μ₂, μ₂)`. -/
lemma two_mul_Gam_le {D s : ℝ} (hs : 0 < s) (μ₁ μ₂ : Measure ℂ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : ∀ᵐ z ∂μ₁, ‖z‖ ≤ D / 2) (h₂ : ∀ᵐ z ∂μ₂, ‖z‖ ≤ D / 2) :
    2 * Gam D s μ₁ μ₂ ≤ Gam D s μ₁ μ₁ + Gam D s μ₂ μ₂ := by
  set c := ENNReal.ofReal (exp (-(s * D ^ 2)) / (2 * s))
  have e12 := Gam_add_const hs μ₁ μ₂ h₁ h₂
  have e11 := Gam_add_const hs μ₁ μ₁ h₁ h₁
  have e22 := Gam_add_const hs μ₂ μ₂ h₂ h₂
  have hG := two_mul_gaussForm_le hs μ₁ μ₂
  refine ENNReal.le_of_add_le_add_right (a := 2 * c) (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) ?_
  calc 2 * Gam D s μ₁ μ₂ + 2 * c = 2 * (Gam D s μ₁ μ₂ + c) := by ring
    _ = ENNReal.ofReal (1 / (2 * s)) * (2 * gaussForm s μ₁ μ₂) := by rw [e12]; ring
    _ ≤ ENNReal.ofReal (1 / (2 * s)) * (gaussForm s μ₁ μ₁ + gaussForm s μ₂ μ₂) := by gcongr
    _ = (Gam D s μ₁ μ₁ + c) + (Gam D s μ₂ μ₂ + c) := by rw [e11, e22]; ring
    _ = Gam D s μ₁ μ₁ + Gam D s μ₂ μ₂ + 2 * c := by ring

/-- **Energy inequality** (Saff-Totik, Lemma I.1.8, in kernel form): for atomless probability measures `μ₁, μ₂`
a.e. supported in `closedBall 0 (D/2)`, `2 Λ(μ₁, μ₂) ≤ Λ(μ₁, μ₁) + Λ(μ₂, μ₂)`. -/
theorem two_mul_Lam_le {D : ℝ} (hD : 0 < D) (μ₁ μ₂ : Measure ℂ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : ∀ᵐ z ∂μ₁, ‖z‖ ≤ D / 2) (h₂ : ∀ᵐ z ∂μ₂, ‖z‖ ≤ D / 2)
    (a₁ : ∀ z, μ₁ {z} = 0) (a₂ : ∀ z, μ₂ {z} = 0) :
    2 * Lam D μ₁ μ₂ ≤ Lam D μ₁ μ₁ + Lam D μ₂ μ₂ := by
  rw [Lam_eq_lintegral_Gam hD μ₁ μ₂ a₂, Lam_eq_lintegral_Gam hD μ₁ μ₁ a₁, Lam_eq_lintegral_Gam hD μ₂ μ₂ a₂,
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    ← lintegral_add_left (measurable_Gam D μ₁ μ₁)]
  exact setLIntegral_mono' measurableSet_Ioi fun s hs => two_mul_Gam_le hs μ₁ μ₂ h₁ h₂

end AuxCommon.Energy
