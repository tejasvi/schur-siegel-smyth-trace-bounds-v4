import Trace86.Statement
import AuxCommon.Resultant

/-!
# Step 3 of Lemma U1: Smith's theorem turns a measure into infinitely many totally positive algebraic integers

`trace_upper_of_measure`: for a probability measure `μ` carried by `[0, 6]` such that, for every nonzero `Q ∈ ℤ[X]`,
`μ` does not charge the roots of `Q`, `log |Q|` is integrable and `∫ log |Q| dμ ≥ 0`, and `∫ x dμ ≤ L`, the set
`TPTraceLe (L + ε)` is infinite for every `ε > 0`. Proof: Smith's theorem (`SmithThm15`) on `[0, 6]` gives distinct monic irreducible `R_k` with real roots in
`[0, 6]` and `tr(R_k)/deg R_k → ∫ x dμ`; all but at most one `R_k` differ from `X`, so their roots are positive;
a root `α_k` of `R_k` is a totally positive algebraic integer with minimal polynomial `R_k`, distinct `R_k` share no
root, and `tr(α_k) ≤ (L + ε) deg(α_k)` for large `k`. `trace_upper_of_measure_eq` takes `∫ x dμ = L`.
-/

open MeasureTheory Set Real Polynomial Filter Topology
open AuxCommon

namespace Trace86

namespace USmith

/-- A monic irreducible polynomial has positive degree. -/
lemma natDegree_ne_zero_of_irreducible_monic {R : ℤ[X]} (hR : Irreducible R) (hRm : R.Monic) :
    R.natDegree ≠ 0 := by
  intro h
  have h1 : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h
  have h2 : R.coeff 0 = 1 := by
    have := hRm.leadingCoeff
    rwa [leadingCoeff, h] at this
  rw [h2, C_1] at h1
  exact hR.not_isUnit (h1 ▸ isUnit_one)

/-- A monic irreducible `R ∈ ℤ[X]` with `R(0) = 0` is `X`. -/
lemma eq_X_of_root_zero {R : ℤ[X]} (hirr : Irreducible R) (hmon : R.Monic) (h0 : R.coeff 0 = 0) : R = X :=
  (eq_of_monic_of_associated monic_X hmon (irreducible_X.associated_of_dvd hirr (X_dvd_iff.2 h0))).symm

/-- Two monic irreducible polynomials of `ℤ[X]` with a common complex root are equal. -/
lemma eq_of_common_root {R S : ℤ[X]} (hR : Irreducible R) (hRm : R.Monic) (hS : Irreducible S) (hSm : S.Monic)
    {α : ℂ} (hαR : aeval α R = 0) (hαS : aeval α S = 0) : R = S := by
  have hdegR := natDegree_ne_zero_of_irreducible_monic hR hRm
  have hmin : IsMinpolyZ R α := ⟨hR, Nat.pos_of_ne_zero hdegR, hαR⟩
  have hdvd := hmin.map_rat_dvd_of_aeval_eq_zero hαS
  have hdvdZ : R ∣ S := by
    rw [(hR.isPrimitive hdegR).dvd_iff_fraction_map_dvd_fraction_map ℚ]
    simpa [algebraMap_int_eq] using hdvd
  exact eq_of_monic_of_associated hRm hSm (hR.associated_of_dvd hS hdvdZ)

/-- For `R ≠ X` monic irreducible with real roots in `[0, B]`, a root is a totally positive algebraic integer with
minimal polynomial `R`. -/
lemma exists_good_root {R : ℤ[X]} {B : ℝ} (hirr : Irreducible R) (hmon : R.Monic)
    (hroots : ∀ z ∈ (toC R).roots, z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ B) (hX : R ≠ X) :
    ∃ α : ℂ, IsIntegral ℤ α ∧ IsMinpolyZ R α ∧ AllRootsPos R := by
  have hdeg := natDegree_ne_zero_of_irreducible_monic hirr hmon
  have hdegC : (toC R).degree ≠ 0 := by
    rw [degree_eq_natDegree (toC_ne_zero hirr.ne_zero), natDegree_toC]
    exact_mod_cast hdeg
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (toC R) hdegC
  have hαR : aeval α R = 0 := by rw [← eval_toC]; exact hα
  refine ⟨α, ⟨R, hmon, ?_⟩, ⟨hirr, Nat.pos_of_ne_zero hdeg, hαR⟩, fun z hz => ?_⟩
  · rwa [aeval_def] at hαR
  · obtain ⟨him, hre0, _⟩ := hroots z hz
    refine ⟨lt_of_le_of_ne hre0 fun h => hX ?_, him⟩
    apply eq_X_of_root_zero hirr hmon
    have hz0 : z = 0 := Complex.ext (by simp [← h]) (by simp [him])
    have h1 := (mem_roots (toC_ne_zero hirr.ne_zero)).1 hz
    rw [hz0, IsRoot.def, eval_toC, aeval_def, eval₂_at_zero, algebraMap_int_eq, eq_intCast,
      Int.cast_eq_zero] at h1
    exact h1

lemma eventually_ne_X {R : ℕ → ℤ[X]} (hinj : Function.Injective R) : ∀ᶠ k in atTop, R k ≠ X := by
  by_cases h : ∃ k₀, R k₀ = X
  · obtain ⟨k₀, hk₀⟩ := h
    filter_upwards [eventually_gt_atTop k₀] with k hk hk'
    exact absurd (hinj (hk'.trans hk₀.symm)) (ne_of_gt hk)
  · push Not at h
    exact Eventually.of_forall h

lemma traceP_eq_sum_re (P : ℤ[X]) : traceP P = ((toC P).roots.map fun z => z.re).sum := by
  rw [traceP]
  exact map_multiset_sum Complex.reAddGroupHom (toC P).roots

end USmith

open USmith

/-- **Step 3 of Lemma U1**: Smith's theorem on `[0, 6]` applied to a probability measure `μ` on `[0, 6]` with the
integrality property and `∫ x dμ ≤ L` gives infinitely many totally positive algebraic integers with
`tr(α) ≤ (L + ε) deg(α)`, for every `ε > 0`. -/
theorem trace_upper_of_measure (hS : SmithThm15) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc 0 6)ᶜ = 0)
    (hint : ∀ Q : ℤ[X], Q ≠ 0 → μ {x | evalR Q x = 0} = 0 ∧ Integrable (fun x => Real.log |evalR Q x|) μ ∧
      0 ≤ ∫ x, Real.log |evalR Q x| ∂μ)
    {L : ℝ} (hL : ∫ x, x ∂μ ≤ L) (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (L + ε)).Infinite := by
  obtain ⟨R, hinj, hR, hconv⟩ := hS 0 6 (by norm_num) μ inferInstance hsupp hint
  have hc := hconv (fun x => x) continuous_id
  have hev1 : ∀ᶠ k in atTop, ((toC (R k)).roots.map fun z => z.re).sum / (R k).natDegree < L + ε :=
    hc.eventually_lt_const (by linarith)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hev1.and (eventually_ne_X hinj))
  have hgood : ∀ k, K ≤ k → ∃ α : ℂ, IsIntegral ℤ α ∧ IsMinpolyZ (R k) α ∧ AllRootsPos (R k) :=
    fun k hk => exists_good_root (hR k).1 (hR k).2.1 (hR k).2.2 (hK k hk).2
  choose! α hα using hgood
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => α (n + K)) ?_ ?_
  · intro m n hmn
    have h1 := (hα (m + K) (by omega)).2.1.2.2
    have h2 := (hα (n + K) (by omega)).2.1.2.2
    simp only at hmn
    rw [hmn] at h1
    have := eq_of_common_root (hR (m + K)).1 (hR (m + K)).2.1 (hR (n + K)).1 (hR (n + K)).2.1 h1 h2
    have := hinj this
    omega
  · intro n
    obtain ⟨hi, hm, hp⟩ := hα (n + K) (by omega)
    refine ⟨hi, R (n + K), hm, hp, ?_⟩
    have hdeg : (0 : ℝ) < (R (n + K)).natDegree := by
      exact_mod_cast Nat.pos_of_ne_zero (natDegree_ne_zero_of_irreducible_monic (hR _).1 (hR _).2.1)
    have h := (hK (n + K) (by omega)).1
    rw [div_lt_iff₀ hdeg] at h
    rw [traceP_eq_sum_re]
    exact h.le

/-- `trace_upper_of_measure` with `∫ x dμ = L`. -/
theorem trace_upper_of_measure_eq (hS : SmithThm15) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc 0 6)ᶜ = 0)
    (hint : ∀ Q : ℤ[X], Q ≠ 0 → μ {x | evalR Q x = 0} = 0 ∧ Integrable (fun x => Real.log |evalR Q x|) μ ∧
      0 ≤ ∫ x, Real.log |evalR Q x| ∂μ)
    {L : ℝ} (hL : ∫ x, x ∂μ = L) (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (L + ε)).Infinite :=
  trace_upper_of_measure hS hsupp hint hL.le ε hε

end Trace86
