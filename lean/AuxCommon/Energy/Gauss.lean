import AuxCommon.Energy.Kernel

/-!
# Positive definiteness of the Gaussian kernel on `ℂ`

`e^{-s|z-w|²} = (4s/π) ∫ e^{-2s|z-u|²} e^{-2s|w-u|²} du`, hence for finite measures `μ₁, μ₂`
`2 G(μ₁, μ₂) ≤ G(μ₁, μ₁) + G(μ₂, μ₂)` with `G(μ, μ') = ∫∫ e^{-s|z-w|²} dμ'(w) dμ(z)`, as lower Lebesgue integrals.
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal

namespace AuxCommon.Energy

/-- `2ab ≤ a² + b²` in `ℝ≥0∞`. -/
lemma two_mul_mul_le_add (a b : ℝ≥0∞) : 2 * a * b ≤ a * a + b * b := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [ENNReal.top_mul_top, top_add]; exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · rw [ENNReal.top_mul_top, add_top]; exact le_top
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have := two_mul_le_add_sq a b
  rw [sq, sq] at this
  exact_mod_cast this

/-- The Gaussian integral over `ℂ`, shifted: `∫ e^{-b|u - m|²} du = π / b`. -/
lemma lintegral_gauss_shift {b : ℝ} (hb : 0 < b) (m : ℂ) :
    ∫⁻ u : ℂ, ENNReal.ofReal (exp (-(b * ‖u - m‖ ^ 2))) = ENNReal.ofReal (π / b) := by
  rw [lintegral_sub_right_eq_self (fun u : ℂ => ENNReal.ofReal (exp (-(b * ‖u‖ ^ 2)))) m]
  have hI : ∫ u : ℂ, exp (-(b * ‖u‖ ^ 2)) = π / b := by
    have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hb
    rw [Complex.finrank_real_complex] at this
    norm_num at this
    simpa [neg_mul] using this
  rw [← hI, ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_integral_ne_zero (by rw [hI]; exact (div_pos pi_pos hb).ne')
  · exact Eventually.of_forall fun u => (exp_pos _).le

/-- The Gaussian factor `e^{-2s|z - u|²}`. -/
noncomputable def gfac (s : ℝ) (u z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (exp (-(2 * s * ‖z - u‖ ^ 2)))

lemma measurable_gfac (s : ℝ) : Measurable fun p : ℂ × ℂ => gfac s p.1 p.2 := by
  unfold gfac; fun_prop

/-- The Gaussian kernel as a convolution square: `e^{-s|z-w|²} = (4s/π) ∫ e^{-2s|z-u|²} e^{-2s|w-u|²} du`. -/
lemma ofReal_exp_eq_lintegral {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ENNReal.ofReal (exp (-(s * ‖z - w‖ ^ 2))) =
      ENNReal.ofReal (4 * s / π) * ∫⁻ u : ℂ, gfac s u z * gfac s u w := by
  have hpar : ∀ u : ℂ, -(2 * s * ‖z - u‖ ^ 2) + -(2 * s * ‖w - u‖ ^ 2) =
      -(s * ‖z - w‖ ^ 2) + -(4 * s * ‖u - (z + w) / 2‖ ^ 2) := by
    intro u
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring
  have h1 : ∀ u : ℂ, gfac s u z * gfac s u w =
      ENNReal.ofReal (exp (-(s * ‖z - w‖ ^ 2))) * ENNReal.ofReal (exp (-(4 * s * ‖u - (z + w) / 2‖ ^ 2))) := by
    intro u
    unfold gfac
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, ← exp_add, hpar]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gauss_shift (by positivity),
    ← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The Gaussian bilinear form `G_s(μ, μ') = ∫∫ e^{-s|z-w|²} dμ'(w) dμ(z)`. -/
noncomputable def gaussForm (s : ℝ) (μ μ' : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ∫⁻ w, ENNReal.ofReal (exp (-(s * ‖z - w‖ ^ 2))) ∂μ' ∂μ

lemma lintegral_gfac_swap (s : ℝ) (μ μ' : Measure ℂ) [SFinite μ] [SFinite μ'] :
    ∫⁻ z, ∫⁻ w, (∫⁻ u : ℂ, gfac s u z * gfac s u w) ∂μ' ∂μ =
      ∫⁻ u : ℂ, (∫⁻ z, gfac s u z ∂μ) * (∫⁻ w, gfac s u w ∂μ') := by
  have hΦ : Measurable fun u => ∫⁻ w, gfac s u w ∂μ' := (measurable_gfac s).lintegral_prod_right'
  calc ∫⁻ z, ∫⁻ w, (∫⁻ u : ℂ, gfac s u z * gfac s u w) ∂μ' ∂μ
      = ∫⁻ z, (∫⁻ u : ℂ, ∫⁻ w, gfac s u z * gfac s u w ∂μ') ∂μ := by
        refine lintegral_congr fun z => ?_
        apply lintegral_lintegral_swap
        unfold gfac
        fun_prop
    _ = ∫⁻ z, (∫⁻ u : ℂ, gfac s u z * ∫⁻ w, gfac s u w ∂μ') ∂μ := by
        refine lintegral_congr fun z => lintegral_congr fun u => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ u : ℂ, ∫⁻ z, gfac s u z * (∫⁻ w, gfac s u w ∂μ') ∂μ := by
        apply lintegral_lintegral_swap
        unfold gfac at *
        fun_prop
    _ = ∫⁻ u : ℂ, (∫⁻ z, gfac s u z ∂μ) * ∫⁻ w, gfac s u w ∂μ' := by
        refine lintegral_congr fun u => ?_
        apply lintegral_mul_const
        unfold gfac
        fun_prop

lemma gaussForm_eq {s : ℝ} (hs : 0 < s) (μ μ' : Measure ℂ) [SFinite μ] [SFinite μ'] :
    gaussForm s μ μ' = ENNReal.ofReal (4 * s / π) *
      ∫⁻ u : ℂ, (∫⁻ z, gfac s u z ∂μ) * (∫⁻ w, gfac s u w ∂μ') := by
  unfold gaussForm
  simp_rw [ofReal_exp_eq_lintegral hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_gfac_swap s μ μ'

/-- Positive definiteness of the Gaussian kernel: `2 G(μ₁, μ₂) ≤ G(μ₁, μ₁) + G(μ₂, μ₂)`. -/
lemma two_mul_gaussForm_le {s : ℝ} (hs : 0 < s) (μ₁ μ₂ : Measure ℂ) [SFinite μ₁] [SFinite μ₂] :
    2 * gaussForm s μ₁ μ₂ ≤ gaussForm s μ₁ μ₁ + gaussForm s μ₂ μ₂ := by
  rw [gaussForm_eq hs, gaussForm_eq hs, gaussForm_eq hs]
  set c := ENNReal.ofReal (4 * s / π)
  have hΦ₁ : Measurable fun u => ∫⁻ z, gfac s u z ∂μ₁ := (measurable_gfac s).lintegral_prod_right'
  set Φ₁ := fun u => ∫⁻ z, gfac s u z ∂μ₁
  set Φ₂ := fun u => ∫⁻ z, gfac s u z ∂μ₂
  calc 2 * (c * ∫⁻ u, Φ₁ u * Φ₂ u) = c * ∫⁻ u, 2 * Φ₁ u * Φ₂ u := by
        have : ∀ u, 2 * Φ₁ u * Φ₂ u = 2 * (Φ₁ u * Φ₂ u) := fun u => mul_assoc _ _ _
        rw [lintegral_congr this, lintegral_const_mul' _ _ (by norm_num)]
        ring
    _ ≤ c * ∫⁻ u, (Φ₁ u * Φ₁ u + Φ₂ u * Φ₂ u) := by
        gcongr with u
        exact two_mul_mul_le_add _ _
    _ = c * (∫⁻ u, Φ₁ u * Φ₁ u) + c * ∫⁻ u, Φ₂ u * Φ₂ u := by
        rw [lintegral_add_left (f := fun u => Φ₁ u * Φ₁ u) (hΦ₁.mul hΦ₁), mul_add]

end AuxCommon.Energy
