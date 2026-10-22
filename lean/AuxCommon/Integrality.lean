import AuxCommon.RootSum
import AuxCommon.Resultant

/-!
# Integrality of a measure from a minimum-principle certificate (Step 2 of Lemma U1 / Lemma 3.1)

Let `μ` be a probability measure on `ℝ` without atoms such that `y ↦ log |z - y|` is `μ`-integrable for every
`z ∈ ℂ`. Let `Q₁, …, Q_J ∈ ℤ[X]` be irreducible, with weights `w_j ≥ 0` and `∑ w_j deg Q_j ≤ 1`, such that
* `∫ log |Q_j| dμ ≥ 0` for every `j`, and
* `∑ w_j log |Q_j(z)| ≤ U_μ(z)` at every `z ∈ ℂ` that is not a root of any `Q_j` (the output of the minimum principle).

Then `log |P|` is `μ`-integrable and `∫ log |P| dμ ≥ 0` for every nonzero `P ∈ ℤ[X]`
(`integrable_and_integral_log_evalR_nonneg`). Proof: `∫ log |P| dμ` is additive over the factorization of `P` into
irreducibles. An irreducible factor associated to some `Q_j` contributes `∫ log |Q_j| dμ ≥ 0`. Another irreducible
factor `i` of positive degree shares no root with any `Q_j`, so by the root sum `∫ log |i| dμ = log |a| + ∑_ρ U_μ(ρ)`
(`a` the leading coefficient of `i`, `ρ` its roots), the minimum-principle bound at each `ρ`, and the resultant bound
`∑_ρ log |Q_j(ρ)| ≥ -(deg Q_j) log |a|`, we get `∫ log |i| dμ ≥ (1 - ∑ w_j deg Q_j) log |a| ≥ 0`. Constant factors
contribute `log |c| ≥ 0`.

For `Q ∈ ℤ[X]`, `(Q.map (Int.castRingHom ℝ)).eval x` is `evalR Q x` and `Q.map (Int.castRingHom ℂ)` is `toC Q` of the
project statements (both abbreviations).
-/

open MeasureTheory Set Real Polynomial

namespace AuxCommon

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [IsProbabilityMeasure μ] in
lemma ae_evalR_ne_zero {P : ℤ[X]} (hP : P ≠ 0) : ∀ᵐ x ∂μ, (P.map (Int.castRingHom ℝ)).eval x ≠ 0 := by
  have hP' : P.map (Int.castRingHom ℝ) ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP
  rw [ae_iff]
  have h := (Polynomial.finite_setOfPred_isRoot hP').measure_zero μ
  simpa using h

lemma integral_log_evalR_mul (hlog : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ)
    {P R : ℤ[X]} (hP : P ≠ 0) (hR : R ≠ 0) :
    ∫ x, log |((P * R).map (Int.castRingHom ℝ)).eval x| ∂μ =
      ∫ x, log |(P.map (Int.castRingHom ℝ)).eval x| ∂μ + ∫ x, log |(R.map (Int.castRingHom ℝ)).eval x| ∂μ := by
  rw [← integral_add (integrable_log_evalR hlog hP) (integrable_log_evalR hlog hR)]
  refine integral_congr_ae ?_
  filter_upwards [ae_evalR_ne_zero (μ := μ) hP, ae_evalR_ne_zero (μ := μ) hR] with x hxP hxR
  rw [Polynomial.map_mul, eval_mul, abs_mul, Real.log_mul (abs_ne_zero.2 hxP) (abs_ne_zero.2 hxR)]

lemma log_abs_leadingCoeff_nonneg {P : ℤ[X]} (hP : P ≠ 0) : 0 ≤ log |(P.leadingCoeff : ℝ)| :=
  Real.log_nonneg (by exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.2 hP))

variable {J : ℕ} (Q : Fin J → ℤ[X]) (w : Fin J → ℝ)

/-- An irreducible polynomial of positive degree that is not associated to any `Q_j` (irreducible) shares no root
with any `Q_j`. -/
lemma eval_ne_zero_of_not_associated (hQirr : ∀ j, Irreducible (Q j)) {i : ℤ[X]} (hi : Irreducible i)
    (hdeg : i.natDegree ≠ 0) (hassoc : ∀ j, ¬ Associated i (Q j)) (j : Fin J) {β : ℂ}
    (hβ : β ∈ (i.map (Int.castRingHom ℂ)).roots) : ((Q j).map (Int.castRingHom ℂ)).eval β ≠ 0 := by
  intro h0
  have hi0 : i ≠ 0 := hi.ne_zero
  have hroot : aeval β i = 0 := by
    have := (mem_roots (toC_ne_zero hi0)).1 hβ
    rwa [IsRoot.def, eval_toC] at this
  have hmin : IsMinpolyZ i β := ⟨hi, Nat.pos_of_ne_zero hdeg, hroot⟩
  have hdvd := hmin.map_rat_dvd_of_aeval_eq_zero (R := Q j) (by rwa [← eval_toC])
  have hdvdZ : i ∣ Q j := by
    rw [(hi.isPrimitive hdeg).dvd_iff_fraction_map_dvd_fraction_map ℚ]
    simpa [algebraMap_int_eq] using hdvd
  exact hassoc j (hi.associated_of_dvd (hQirr j) hdvdZ)

/-- The contribution of one irreducible factor. -/
lemma integral_log_evalR_irreducible_nonneg (hlog : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ)
    (hw : ∀ j, 0 ≤ w j) (hdeg : ∑ j, w j * (Q j).natDegree ≤ 1) (hQirr : ∀ j, Irreducible (Q j))
    (hC2 : ∀ j, 0 ≤ ∫ x, log |((Q j).map (Int.castRingHom ℝ)).eval x| ∂μ)
    (hmin : ∀ z : ℂ, (∀ j, ((Q j).map (Int.castRingHom ℂ)).eval z ≠ 0) →
      ∑ j, w j * log ‖((Q j).map (Int.castRingHom ℂ)).eval z‖ ≤ ∫ y, log ‖z - (y : ℂ)‖ ∂μ)
    {i : ℤ[X]} (hi : Irreducible i) : 0 ≤ ∫ x, log |(i.map (Int.castRingHom ℝ)).eval x| ∂μ := by
  have hi0 : i ≠ 0 := hi.ne_zero
  by_cases hdeg0 : i.natDegree = 0
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.1 hdeg0
    have hc : c ≠ 0 := by rintro rfl; simp at hi0
    simp only [Polynomial.map_C, eval_C]
    simp only [eq_intCast]
    rw [integral_const, probReal_univ, one_smul]
    exact Real.log_nonneg (by exact_mod_cast Int.one_le_abs hc)
  by_cases hassoc : ∃ j, Associated i (Q j)
  · obtain ⟨j, u, hu⟩ := hassoc
    have habs : ∀ x : ℝ, |(i.map (Int.castRingHom ℝ)).eval x| = |((Q j).map (Int.castRingHom ℝ)).eval x| := by
      intro x
      rw [← hu, Polynomial.map_mul, eval_mul, abs_mul]
      obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
      rw [← hru, Polynomial.map_C, eval_C, eq_intCast]
      rcases Int.isUnit_iff.1 hr with rfl | rfl <;> simp
    simp_rw [habs]
    exact hC2 j
  push Not at hassoc
  have hroot := eval_ne_zero_of_not_associated Q hQirr hi hdeg0 hassoc
  rw [integral_log_evalR hlog hi0]
  have hlc := log_abs_leadingCoeff_nonneg hi0
  set L := log |(i.leadingCoeff : ℝ)| with hL
  have h1 : ∀ β ∈ (i.map (Int.castRingHom ℂ)).roots,
      ∑ j, w j * log ‖((Q j).map (Int.castRingHom ℂ)).eval β‖ ≤ ∫ y, log ‖β - (y : ℂ)‖ ∂μ :=
    fun β hβ => hmin β fun j => hroot j hβ
  have h2 := Multiset.sum_map_le_sum_map _ _ h1
  rw [Multiset.sum_map_sum] at h2
  have h3 : ∀ j, w j * (-(((Q j).natDegree : ℝ) * L)) ≤
      ((i.map (Int.castRingHom ℂ)).roots.map fun β => w j * log ‖((Q j).map (Int.castRingHom ℂ)).eval β‖).sum := by
    intro j
    rw [Multiset.sum_map_mul_left]
    exact mul_le_mul_of_nonneg_left
      (neg_mul_log_le_sum_log_norm_eval hi0 (Q j) _ le_rfl fun β hβ => hroot j hβ) (hw j)
  have h4 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
  have h5 : ∑ j, w j * (-(((Q j).natDegree : ℝ) * L)) = -((∑ j, w j * (Q j).natDegree) * L) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h5] at h4
  have h6 : (∑ j, w j * ((Q j).natDegree : ℝ)) * L ≤ L := by nlinarith
  linarith

/-- **Integrality** (Step 2 of Lemma U1 / Lemma 3.1): under the hypotheses above, `log |P|` is `μ`-integrable and
`∫ log |P| dμ ≥ 0` for every nonzero `P ∈ ℤ[X]`. -/
theorem integrable_and_integral_log_evalR_nonneg
    (hlog : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ)
    (hw : ∀ j, 0 ≤ w j) (hdeg : ∑ j, w j * (Q j).natDegree ≤ 1) (hQirr : ∀ j, Irreducible (Q j))
    (hC2 : ∀ j, 0 ≤ ∫ x, log |((Q j).map (Int.castRingHom ℝ)).eval x| ∂μ)
    (hmin : ∀ z : ℂ, (∀ j, ((Q j).map (Int.castRingHom ℂ)).eval z ≠ 0) →
      ∑ j, w j * log ‖((Q j).map (Int.castRingHom ℂ)).eval z‖ ≤ ∫ y, log ‖z - (y : ℂ)‖ ∂μ)
    {P : ℤ[X]} (hP : P ≠ 0) :
    Integrable (fun x => log |(P.map (Int.castRingHom ℝ)).eval x|) μ ∧
      0 ≤ ∫ x, log |(P.map (Int.castRingHom ℝ)).eval x| ∂μ := by
  refine ⟨integrable_log_evalR hlog hP, ?_⟩
  revert hP
  refine WfDvdMonoid.induction_on_irreducible P (fun h => absurd rfl h) (fun u hu _ => ?_)
    (fun a i ha hi ih _ => ?_)
  · obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.1 hu
    rcases Int.isUnit_iff.1 hr with rfl | rfl <;> simp
  · rw [integral_log_evalR_mul hlog hi.ne_zero ha]
    exact add_nonneg (integral_log_evalR_irreducible_nonneg Q w hlog hw hdeg hQirr hC2 hmin hi) (ih ha)

end AuxCommon
