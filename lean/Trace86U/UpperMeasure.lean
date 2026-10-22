import Trace86U.TraceSound
import Trace86U.BudgetSound
import Trace86.Arcsine
import AuxCommon.RootSum
import AuxCommon.Energy.PotentialSum

/-!
# The measure `μ = (1 - ε) μ₀ + ε ω` of the 86a upper bound

`μ₀ = G dx` (`G = pwLin NN eR GR`, unit-mass hats with weights `w_k`, `∫ G = 1`), `ω = omega06` (the arcsine measure of
`[0, 6]`), `ε = 1/100000`. Facts: probability, support in `[0, 6]`, no atoms, `log |z - y|` integrable, continuity of the
potential on `ℂ` (MinPrinciple's premise), the potential on `[0, 6]`: `U_μ(x) = (1 - ε)(-2 U'(x)) + ε log(3/2)`, and
the mean `∫ x dμ = λ_U` (from `traceOK`).
-/

open Polynomial Set MeasureTheory Filter
open scoped ENNReal

namespace Trace86.UCert

open T86UCore AuxCommon

/-- The density of `μ₀`. -/
noncomputable def G0 (y : ℝ) : ℝ := pwLin NN eR GR y

theorem G0_nonneg (y : ℝ) : 0 ≤ G0 y := pwLin_nonneg (fun k _ => GR_nonneg k) y

theorem measurable_G0 : Measurable G0 := measurable_pwLin NN eR GR

/-- An upper bound for the node values. -/
noncomputable def Gm : ℝ := ∑ k ∈ Finset.range (NN + 1), GR k

theorem Gm_nonneg : 0 ≤ Gm := Finset.sum_nonneg (fun i _ => GR_nonneg i)

theorem GR_le_Gm {k : ℕ} (hk : k ≤ NN) : GR k ≤ Gm :=
  Finset.single_le_sum (f := GR) (fun i _ => GR_nonneg i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem G0_le (y : ℝ) : G0 y ≤ Gm := pwLin_le eR_lt (fun k _ => GR_nonneg k) (fun k hk => GR_le_Gm hk) y

theorem eR_NN : eR NN = 6 := by unfold eR; rw [nodes_last]; norm_num

theorem G0_zero_off {y : ℝ} (hy : y ∉ Icc (0 : ℝ) 6) : G0 y = 0 := by
  apply pwLin_eq_zero_of_notMem eR_lt
  rw [eR_zero, eR_NN]
  simp only [mem_Icc, not_and_or, not_le] at hy
  rcases hy with h | h
  · exact Or.inl h
  · exact Or.inr h.le

theorem integrable_G0 : Integrable G0 := integrable_pwLin NN eR GR

theorem integral_G0 : ∫ y, G0 y = 1 := by
  unfold G0
  rw [integral_pwLin eR_lt, mass_eq_one]

/-- `μ₀ = G dx`. -/
noncomputable def mu0 : Measure ℝ := volume.withDensity (fun y => ENNReal.ofReal (G0 y))

instance : IsProbabilityMeasure mu0 := by
  constructor
  rw [mu0, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_G0 (Eventually.of_forall G0_nonneg), integral_G0,
    ENNReal.ofReal_one]

instance : NullSingletonClass mu0 := nullSingletonClass_withDensity volume _

theorem mu0_compl : mu0 (Icc (0 : ℝ) 6)ᶜ = 0 := by
  rw [mu0, withDensity_apply _ measurableSet_Icc.compl]
  apply setLIntegral_eq_zero measurableSet_Icc.compl
  intro y hy
  simp [G0_zero_off hy]

theorem mu0_ball (x s : ℝ) (hs : 0 < s) (_hs1 : s ≤ 1) :
    (mu0 (Ioo (x - s) (x + s))).toReal ≤ (2 * Gm) * s ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have h : mu0 (Ioo (x - s) (x + s)) ≤ ENNReal.ofReal Gm * volume (Ioo (x - s) (x + s)) := by
    rw [mu0, withDensity_apply _ measurableSet_Ioo]
    calc ∫⁻ y in Ioo (x - s) (x + s), ENNReal.ofReal (G0 y)
        ≤ ∫⁻ _ in Ioo (x - s) (x + s), ENNReal.ofReal Gm :=
          lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (G0_le y))
      _ = ENNReal.ofReal Gm * volume (Ioo (x - s) (x + s)) := by rw [setLIntegral_const]
  rw [Real.volume_Ioo, show x + s - (x - s) = 2 * s by ring] at h
  calc (mu0 (Ioo (x - s) (x + s))).toReal ≤ (ENNReal.ofReal Gm * ENNReal.ofReal (2 * s)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
    _ = Gm * (2 * s) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal Gm_nonneg, ENNReal.toReal_ofReal (by positivity)]
    _ = 2 * Gm * s := by ring

theorem hlog0 (z : ℂ) : Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) mu0 :=
  AuxCommon.Energy.integrable_log_norm_sub_of_ball_le mu0_compl (mul_nonneg (by norm_num) Gm_nonneg) one_pos
    mu0_ball z

/-- `ε = EPSN / EPSD`. -/
noncomputable def epsU : ℝ := (EPSN : ℝ) / EPSD

theorem epsU_pos : 0 < epsU := by unfold epsU EPSN EPSD; norm_num

theorem epsU_lt_one : epsU < 1 := by unfold epsU EPSN EPSD; norm_num

/-- `(1 - ε) c₀ = ε log(3/2)`. -/
theorem epsU_c0R : (1 - epsU) * c0R = epsU * Real.log (3 / 2) := by
  unfold epsU c0R EPSN EPSD
  norm_num
  ring

/-- `μ = (1 - ε) μ₀ + ε ω`. -/
noncomputable def muU : Measure ℝ := ENNReal.ofReal (1 - epsU) • mu0 + ENNReal.ofReal epsU • omega06

instance : IsProbabilityMeasure muU := isProbabilityMeasure_mix epsU_pos.le epsU_lt_one.le

instance : NullSingletonClass muU := nullSingletonClass_mix

theorem muU_compl : muU (Icc (0 : ℝ) 6)ᶜ = 0 := mix_apply_eq_zero mu0_compl omega06_compl_Icc

theorem hlogU (z : ℂ) : Integrable (fun y : ℝ => Real.log ‖z - (y : ℂ)‖) muU :=
  integrable_log_mix hlog0 integrable_log_omega06 z

/-- **Continuity of the potential of `μ` on `ℂ`** (MinPrinciple's premise). -/
theorem continuous_logPot_muU : Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂muU := by
  show Continuous fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂(ENNReal.ofReal (1 - epsU) • mu0 +
    ENNReal.ofReal epsU • AuxCommon.Energy.arcsineMeasure 3 3)
  exact AuxCommon.Energy.continuous_logPot_ball_add_arcsine ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top mu0_compl
    (mul_nonneg (by norm_num) Gm_nonneg) one_pos mu0_ball (by norm_num)

theorem norm_ofReal_sub (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- `U_{μ₀}(x) = -2 U'(x)` on `ℝ` (closed form). -/
theorem logPot_mu0_real (x : ℝ) : ∫ y, Real.log ‖(x : ℂ) - (y : ℂ)‖ ∂mu0 = -2 * UR x := by
  rw [mu0, integral_withDensity_eq_integral_toReal_smul measurable_G0.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have h1 : (fun y : ℝ => (ENNReal.ofReal (G0 y)).toReal • Real.log ‖(x : ℂ) - (y : ℂ)‖) =
      fun y => Real.log |x - y| * pwLin NN eR GR y := by
    funext y
    rw [ENNReal.toReal_ofReal (G0_nonneg y), smul_eq_mul, norm_ofReal_sub, G0, mul_comm]
  rw [h1, integral_log_mul_pwLin eR_lt GR_zero GR_NN x]
  unfold UR CR
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The potential of `μ` on `[0, 6]`. -/
theorem logPot_muU_real {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 6) :
    ∫ y, Real.log ‖(x : ℂ) - (y : ℂ)‖ ∂muU = (1 - epsU) * (-2 * UR x) + epsU * Real.log (3 / 2) := by
  rw [muU, logPot_mix hlog0 integrable_log_omega06 epsU_pos.le epsU_lt_one.le, logPot_mu0_real]
  have h := logPot_omega06_of_mem_Icc hx
  have e : (fun y : ℝ => Real.log ‖(x : ℂ) - (y : ℂ)‖) = fun y => Real.log |x - y| := by
    funext y
    rw [norm_ofReal_sub]
  rw [e, h]

theorem integrable_id_mu0 : Integrable (fun x : ℝ => x) mu0 :=
  integrable_of_continuous_of_compl_Icc mu0_compl continuous_id

theorem mean_mu0 : ∫ x, x ∂mu0 = ((traceNum : ℕ) : ℝ) / (3 * ((WD : ℝ) * 10 ^ 12)) := by
  rw [mu0, integral_withDensity_eq_integral_toReal_smul measurable_G0.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), ← integral_mul_id_pwLin_eq]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (G0_nonneg y), smul_eq_mul, G0, mul_comm]

/-- **The mean** `∫ x dμ = λ_U` (condition (T)). -/
theorem mean_muU (htr : traceOK = true) : ∫ x, x ∂muU = lamU := by
  rw [muU, integral_mix integrable_id_mu0 integrable_id_omega06 epsU_pos.le epsU_lt_one.le, mean_mu0,
    integral_id_omega06]
  have h := htr
  unfold traceOK at h
  rw [beq_iff_eq] at h
  have hR : (((EPSD - EPSN) * traceNum * lamUDen + 9 * EPSN * WD * DEC * lamUDen : ℕ) : ℝ) =
      ((3 * WD * DEC * EPSD * lamUNum : ℕ) : ℝ) := by rw [h]
  have hED : ((EPSD - EPSN : ℕ) : ℝ) = (EPSD : ℝ) - EPSN := by
    rw [Nat.cast_sub (by unfold EPSD EPSN; norm_num)]
  push_cast [hED] at hR
  have hWD : (0 : ℝ) < WD := by unfold WD; norm_num
  generalize ((traceNum : ℕ) : ℝ) = T at hR ⊢
  generalize (WD : ℝ) = W at hR hWD ⊢
  unfold epsU lamU
  rw [show ((DEC : ℕ) : ℝ) = 10 ^ 12 by unfold DEC; norm_num] at hR
  unfold EPSN EPSD lamUNum lamUDen at hR
  unfold EPSN EPSD
  push_cast at hR ⊢
  field_simp
  linarith

end Trace86.UCert
