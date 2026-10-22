import AuxCommon.Averaging
import AuxCommon.Northcott
import Trace86.Statement

/-!
# Reduction of the lower bound to the auxiliary inequality (trace version of the companion Mahler-measure formalization's reduction)

* `IsMinpolyZ.abs_leadingCoeff_eq_one`: the minimal polynomial over `ℤ` of an algebraic integer has leading
  coefficient `±1`.
* `lemmaT1`: the effective form of Lemma T1 of the paper: if `F(x) = x - m - ∑ cⱼ log|Qⱼ(x)| - λ (2 U_ν(x) - I(ν)) ≥ 0` on
  `(0, ∞)` off the roots, then `tr(α)/n ≥ m - λ (1 + log (2Kn)) / n` for every totally positive algebraic integer `α`
  of degree `n ≥ 1/(2K)` that is not a root of a `Qⱼ` (from `EnergySmoothing`, the resultant and discriminant bounds).
* `cor_trace`: `TPTraceLe (m - ε)` is finite for every `ε > 0`.
-/

open Polynomial MeasureTheory Filter Topology
open AuxCommon

namespace AuxCommon.IsMinpolyZ

variable {P : ℤ[X]} {α : ℂ}

/-- The minimal polynomial over `ℤ` of an algebraic integer is monic up to sign. -/
theorem abs_leadingCoeff_eq_one (hint : IsIntegral ℤ α) (hP : IsMinpolyZ P α) : |P.leadingCoeff| = 1 := by
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hP.2.2
  have hmon := minpoly.monic hint
  rcases hP.1.isUnit_or_isUnit hq with hu | hu
  · exact absurd hu (minpoly.not_isUnit ℤ α)
  · obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [hq, leadingCoeff_mul, hmon.leadingCoeff, one_mul, leadingCoeff_C]
    rcases Int.isUnit_iff.mp hr with rfl | rfl <;> simp

theorem log_abs_leadingCoeff_eq_zero (hint : IsIntegral ℤ α) (hP : IsMinpolyZ P α) :
    Real.log |(P.leadingCoeff : ℝ)| = 0 := by
  have h := hP.abs_leadingCoeff_eq_one hint
  have : |(P.leadingCoeff : ℝ)| = 1 := by exact_mod_cast h
  rw [this, Real.log_one]

end AuxCommon.IsMinpolyZ

namespace Trace86

/-- The trace as a sum over the (distinct) roots of a minimal polynomial. -/
theorem traceP_eq_sum {P : ℤ[X]} {α : ℂ} (hP : IsMinpolyZ P α) : traceP P = ∑ β ∈ rootsC P, β.re := by
  have h : (rootsC P).val.sum = ∑ β ∈ rootsC P, β := by
    rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
  rw [traceP, ← hP.val_rootsC, h, Complex.re_sum]

theorem posLog_le_self {x : ℝ} (hx : 0 ≤ x) : Real.posLog x ≤ x := by
  rw [Real.posLog, max_le_iff]
  refine ⟨hx, ?_⟩
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  · have := Real.log_le_sub_one_of_pos hx'
    linarith

/-- **Lemma T1 of the paper, effective form.** -/
theorem lemmaT1 (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (lam m K : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hc : ∀ j, 0 ≤ c j) (hlam : 0 ≤ lam)
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν))
    {P : ℤ[X]} {α : ℂ} (hint : IsIntegral ℤ α) (hP : IsMinpolyZ P α) (hpos : AllRootsPos P)
    (hnr : ∀ j, aeval α (Q j) ≠ 0) (hn : 1 / (2 * K) ≤ P.natDegree) :
    m - lam * (1 + Real.log (2 * K * P.natDegree)) / P.natDegree ≤ traceP P / P.natDegree := by
  classical
  have hnR : (0 : ℝ) < P.natDegree := by exact_mod_cast hP.2.1
  have hcard : (rootsC P).card = P.natDegree := hP.card_rootsC
  have hLa : Real.log |(P.leadingCoeff : ℝ)| = 0 := hP.log_abs_leadingCoeff_eq_zero hint
  -- Step 1: the auxiliary inequality at each conjugate (a positive real number)
  have hle : ∀ β ∈ rootsC P, m + ∑ j, c j * Real.log ‖eval β (toC (Q j))‖ +
      lam * (2 * logPot ν β - logEnergy ν) ≤ β.re := by
    intro β hβ
    obtain ⟨h1, h2⟩ := hpos β (Multiset.mem_toFinset.mp hβ)
    have hβre : ((β.re : ℝ) : ℂ) = β := Complex.ext (by simp) (by simp [h2])
    have := hF β.re h1 (fun j => by rw [hβre]; exact hP.eval_ne_zero_of_mem_rootsC (hnr j) hβ)
    rw [hβre] at this
    linarith
  -- Step 2: sum over the conjugates
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
    Finset.sum_comm, ← Finset.mul_sum] at hsum
  simp only [← Finset.mul_sum] at hsum
  -- Step 3: the resultant bound (`log |a| = 0`)
  have hA : 0 ≤ ∑ j, c j * ∑ β ∈ rootsC P, Real.log ‖eval β (toC (Q j))‖ := by
    apply Finset.sum_nonneg
    intro j _
    have h1 := hP.sum_log_norm_eval_ge (hnr j)
    rw [hLa, mul_zero, neg_zero] at h1
    exact mul_nonneg (hc j) h1
  -- Step 4: energy smoothing with r = 1/(2Kn) and the discriminant bound
  have hEb := hP.energy_sum_ge hE ν hK hsupp hdisc hn
  rw [hLa, mul_zero, zero_sub] at hEb
  have hlamE := mul_le_mul_of_nonneg_left hEb hlam
  rw [traceP_eq_sum hP, le_div_iff₀ hnR, sub_mul, div_mul_cancel₀ _ hnR.ne']
  nlinarith

/-- **Corollary (finiteness).** For every `ε > 0` only finitely many totally positive algebraic integers satisfy
`tr(α) ≤ (m - ε) deg(α)`. -/
theorem cor_trace (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (lam m K : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hQ : ∀ j, Q j ≠ 0) (hc : ∀ j, 0 ≤ c j) (hlam : 0 ≤ lam)
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν))
    (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (m - ε)).Finite := by
  obtain ⟨n₀, hn₀⟩ := exists_error_lt lam K ε hK hε
  refine ((finite_setOf_exists_aeval_eq_zero Q hQ).union
    (finite_minpolyZ_logHeight_le (max n₀ ⌈1 / (2 * K)⌉₊) (m - ε))).subset ?_
  rintro α ⟨hint, P, hP, hpos, hlow⟩
  by_cases hroot : ∃ j, aeval α (Q j) = 0
  · exact Or.inl hroot
  · refine Or.inr ?_
    push Not at hroot
    have hnR : (0 : ℝ) < P.natDegree := by exact_mod_cast hP.2.1
    -- `log M(P) ≤ tr(α)`: `log |a| = 0` and `log⁺ β ≤ β`
    have hM : Real.log (toC P).mahlerMeasure ≤ traceP P := by
      rw [hP.log_mahlerMeasure_eq, hP.log_abs_leadingCoeff_eq_zero hint, zero_add, traceP_eq_sum hP]
      refine Finset.sum_le_sum (fun β hβ => ?_)
      obtain ⟨h1, h2⟩ := hpos β (Multiset.mem_toFinset.mp hβ)
      have hβre : ((β.re : ℝ) : ℂ) = β := Complex.ext (by simp) (by simp [h2])
      have hnorm : ‖β‖ = β.re := by
        conv_lhs => rw [← hβre]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
      rw [hnorm]
      exact posLog_le_self h1.le
    refine ⟨P, hP, ?_, ?_⟩
    · by_contra hdeg
      push Not at hdeg
      have hn1 : 1 / (2 * K) ≤ P.natDegree :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hdeg.le)
      have h22 := lemmaT1 hE Q c lam m K ν hc hlam hK hsupp hdisc hF hint hP hpos hroot hn1
      have herr := hn₀ P.natDegree ((le_max_left _ _).trans hdeg.le)
      have hlow' : traceP P / P.natDegree ≤ m - ε := by rw [div_le_iff₀ hnR]; exact hlow
      linarith
    · rw [div_le_iff₀ hnR]
      exact hM.trans hlow

end Trace86
