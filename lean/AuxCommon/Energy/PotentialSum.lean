import AuxCommon.Energy.Continuity
import AuxCommon.Energy.Arcsine

/-!
# Potentials of combinations `a • μ₀ + b • ω`

`continuous_logPot_add_smul`: the potential of `a • μ₁ + b • μ₂` is `a U_{μ₁} + b U_{μ₂}` (when the kernel is
integrable for both), hence continuous if both are. `continuous_logPot_ball_add_arcsine`: the case of a measure with
an interval bound (e.g. a bounded density) plus the arcsine measure, as in the upper-bound measures
`μ = (1 - ε) μ₀ + ε ω` of the trace (86a) and areal Mahler-measure upper bounds (MinPrinciple's continuity
hypothesis).
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal Topology

namespace AuxCommon.Energy

lemma logPot_add_smul {μ₁ μ₂ : Measure ℝ} {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {z : ℂ}
    (h1 : Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) μ₁)
    (h2 : Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) μ₂) :
    ∫ y, Real.log ‖z - (y : ℂ)‖ ∂(a • μ₁ + b • μ₂) =
      a.toReal * (∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ₁) + b.toReal * ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ₂ := by
  rw [integral_add_measure (h1.smul_measure ha) (h2.smul_measure hb), integral_smul_measure,
    integral_smul_measure, smul_eq_mul, smul_eq_mul]

theorem continuous_logPot_add_smul {μ₁ μ₂ : Measure ℝ} {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h1 : ∀ z : ℂ, Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) μ₁)
    (h2 : ∀ z : ℂ, Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) μ₂)
    (c1 : Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ₁)
    (c2 : Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ₂) :
    Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂(a • μ₁ + b • μ₂) := by
  have : (fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂(a • μ₁ + b • μ₂)) =
      fun z => a.toReal * (∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ₁) + b.toReal * ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ₂ := by
    ext z
    exact logPot_add_smul ha hb (h1 z) (h2 z)
  rw [this]
  exact (continuous_const.mul c1).add (continuous_const.mul c2)

/-- Continuity of the potential of `a • μ₀ + b • ω`, `μ₀` finite on `ℝ`, supported in `[a₀, b₀]`, with
`μ₀(x - s, x + s) ≤ K s^γ`, and `ω` the arcsine measure of `[c - R, c + R]` (`R > 0`). -/
theorem continuous_logPot_ball_add_arcsine {μ₀ : Measure ℝ} [IsFiniteMeasure μ₀] {a₀ b₀ K γ c R : ℝ}
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hsupp : μ₀ (Icc a₀ b₀)ᶜ = 0) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hball : ∀ (x s : ℝ), 0 < s → s ≤ 1 → (μ₀ (Ioo (x - s) (x + s))).toReal ≤ K * s ^ γ) (hR : 0 < R) :
    Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂(a • μ₀ + b • arcsineMeasure c R) :=
  continuous_logPot_add_smul ha hb (integrable_log_norm_sub_of_ball_le hsupp hK hγ hball)
    (integrable_log_norm_sub_arcsineMeasure hR) (continuous_logPot_of_ball_le hsupp hK hγ hball)
    (continuous_logPot_arcsineMeasure hR)

end AuxCommon.Energy
