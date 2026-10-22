import Mathlib

/-!
# Root sums of `log |Q|` against measures on `ℝ` (step 2 of Lemma U1), and mixture algebra

For a finite measure `μ` on `ℝ` without atoms such that `y ↦ log |z - y|` is `μ`-integrable for every `z ∈ ℂ`, and a
nonzero `Q ∈ ℤ[X]` (or `P ∈ ℂ[X]`): `log |Q|` is `μ`-integrable (`integrable_log_evalR`) and
`∫ log |Q| dμ = μ(ℝ) log |lc Q| + ∑_ρ U_μ(ρ)` over the complex roots `ρ` of `Q` with multiplicity, where
`U_μ(z) = ∫ log |z - y| dμ(y)` (`integral_log_evalR_of_finite`; for a probability measure `integral_log_evalR`).
Proof: `Q = lc ∏ (x - ρ)` over `ℂ`, so `log |Q(x)| = log |lc| + ∑ log |x - ρ|` off the finitely many real roots, which
form a `μ`-null set.

The hypothesis "no atoms" cannot be dropped: for `μ = δ_{x₀}` at a real root `x₀` of `Q` every `log |z - y|` is
`μ`-integrable, but `∫ log |Q| dμ = log 0 = 0` in Lean while the root sum is `log |Q'(x₀)|` in general.

For `Q ∈ ℤ[X]`, `(Q.map (Int.castRingHom ℝ)).eval x` is `evalR Q x` and `Q.map (Int.castRingHom ℂ)` is `toC Q` of the
project statements (both abbreviations).

Mixtures `ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω` (`0 ≤ t ≤ 1`): probability, null sets, no atoms,
integrability and the splitting `∫ f = (1 - t) ∫ f dμ₀ + t ∫ f dω` (`integral_mix`, `logPot_mix`,
`integral_log_evalR_mix`). Continuity of potentials is not here (see `AuxCommon.Energy.continuous_logPot_add_smul`).
-/

open MeasureTheory Set Real Polynomial

namespace AuxCommon

section Poly

variable {μ : Measure ℝ}

lemma integrable_integral_multiset_sum_log (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    (s : Multiset ℂ) :
    Integrable (fun x : ℝ => (s.map fun ρ => log ‖(x : ℂ) - ρ‖).sum) μ ∧
      ∫ x, (s.map fun ρ => log ‖(x : ℂ) - ρ‖).sum ∂μ = (s.map fun ρ => ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : Integrable (fun x : ℝ => log ‖(x : ℂ) - a‖) μ := by
      simp_rw [norm_sub_rev _ a]; exact hlog a
    simp only [Multiset.map_cons, Multiset.sum_cons]
    refine ⟨ha.add ih.1, ?_⟩
    rw [integral_add ha ih.1, ih.2]
    simp_rw [norm_sub_rev _ a]

/-- For a nonzero `P ∈ ℂ[X]`: `log |P(x)| = log |lc P| + ∑_ρ log |x - ρ|` for `μ`-a.e. real `x`. -/
lemma ae_log_norm_eval_eq [NullSingletonClass μ] {P : ℂ[X]} (hP : P ≠ 0) :
    ∀ᵐ x : ℝ ∂μ,
      log ‖P.eval (x : ℂ)‖ = log ‖P.leadingCoeff‖ + (P.roots.map fun ρ => log ‖(x : ℂ) - ρ‖).sum := by
  have h : ∀ᵐ x : ℝ ∂μ, ∀ ρ ∈ P.roots.toFinset, (x : ℂ) ≠ ρ := by
    rw [Finset.eventually_all]
    intro ρ _
    rw [ae_iff]
    refine measure_mono_null (t := {ρ.re}) ?_ (measure_singleton _)
    intro x hx
    simp only [ne_eq, Decidable.not_not, mem_ofPred_eq] at hx
    simp [← hx]
  filter_upwards [h] with x hx
  have hne : ∀ y ∈ P.roots.map (fun ρ => ‖(x : ℂ) - ρ‖), y ≠ 0 := by
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.1 hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 (hx ρ (Multiset.mem_toFinset.2 hρ)))
  rw [(IsAlgClosed.splits P).eval_eq_prod_roots, norm_mul, Multiset.norm_prod, Multiset.map_map]
  simp only [Function.comp_def]
  rw [log_mul (norm_ne_zero_iff.2 (leadingCoeff_ne_zero.2 hP)) (Multiset.prod_ne_zero fun h0 => hne 0 h0 rfl),
    log_multiset_prod hne, Multiset.map_map]
  rfl

variable [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem integrable_log_norm_eval (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {P : ℂ[X]} (hP : P ≠ 0) : Integrable (fun x : ℝ => log ‖P.eval (x : ℂ)‖) μ :=
  ((integrable_const _).add (integrable_integral_multiset_sum_log hlog P.roots).1).congr
    ((ae_log_norm_eval_eq hP).mono fun _ hx => hx.symm)

/-- `∫ log |P| dμ = log |lc P| + ∑_ρ U_μ(ρ)` over the complex roots `ρ` of `P` (with multiplicity). -/
theorem integral_log_norm_eval (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {P : ℂ[X]} (hP : P ≠ 0) :
    ∫ x, log ‖P.eval (x : ℂ)‖ ∂μ =
      μ.real univ * log ‖P.leadingCoeff‖ + (P.roots.map fun ρ => ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ).sum := by
  rw [integral_congr_ae (ae_log_norm_eval_eq hP),
    integral_add (integrable_const _) (integrable_integral_multiset_sum_log hlog P.roots).1,
    (integrable_integral_multiset_sum_log hlog P.roots).2, integral_const, smul_eq_mul]

/-- Lower bound for `P ∈ ℂ[X]`: if `U_μ ≥ m` at every root, `∫ log |P| dμ ≥ μ(ℝ) log |lc P| + deg P · m`. -/
theorem le_integral_log_norm_eval (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {P : ℂ[X]} (hP : P ≠ 0) {m : ℝ} (hm : ∀ ρ ∈ P.roots, m ≤ ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ) :
    μ.real univ * log ‖P.leadingCoeff‖ + P.natDegree * m ≤ ∫ x, log ‖P.eval (x : ℂ)‖ ∂μ := by
  rw [integral_log_norm_eval hlog hP]
  have h := Multiset.sum_map_le_sum_map (s := P.roots) (fun _ => m) _ hm
  rw [Multiset.map_const', Multiset.sum_replicate, IsAlgClosed.card_roots_eq_natDegree, nsmul_eq_mul] at h
  linarith

lemma eval_map_int_complex (Q : ℤ[X]) (x : ℝ) :
    (Q.map (Int.castRingHom ℂ)).eval (x : ℂ) = (((Q.map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) := by
  have hmap : Q.map (Int.castRingHom ℂ) = (Q.map (Int.castRingHom ℝ)).map Complex.ofRealHom := by
    rw [Polynomial.map_map]
    congr 1
  rw [hmap, eval_map]
  exact eval₂_at_apply _ _

lemma abs_eval_map_int (Q : ℤ[X]) (x : ℝ) :
    |(Q.map (Int.castRingHom ℝ)).eval x| = ‖(Q.map (Int.castRingHom ℂ)).eval (x : ℂ)‖ := by
  rw [eval_map_int_complex, Complex.norm_real, Real.norm_eq_abs]

lemma map_int_complex_ne_zero {Q : ℤ[X]} (hQ : Q ≠ 0) : Q.map (Int.castRingHom ℂ) ≠ 0 :=
  (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hQ

lemma norm_leadingCoeff_map_int (Q : ℤ[X]) :
    ‖(Q.map (Int.castRingHom ℂ)).leadingCoeff‖ = |(Q.leadingCoeff : ℝ)| := by
  rw [leadingCoeff_map_of_injective (RingHom.injective_int _), eq_intCast, Complex.norm_intCast]

/-- `log |Q|` is `μ`-integrable for every nonzero `Q ∈ ℤ[X]`. -/
theorem integrable_log_evalR (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) : Integrable (fun x => log |(Q.map (Int.castRingHom ℝ)).eval x|) μ := by
  simp_rw [abs_eval_map_int]
  exact integrable_log_norm_eval hlog (map_int_complex_ne_zero hQ)

/-- `∫ log |Q| dμ = μ(ℝ) log |lc Q| + ∑_ρ U_μ(ρ)` over the complex roots `ρ` of a nonzero `Q ∈ ℤ[X]`. -/
theorem integral_log_evalR_of_finite (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ =
      μ.real univ * log |(Q.leadingCoeff : ℝ)| +
        ((Q.map (Int.castRingHom ℂ)).roots.map fun ρ => ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ).sum := by
  simp_rw [abs_eval_map_int]
  rw [integral_log_norm_eval hlog (map_int_complex_ne_zero hQ), norm_leadingCoeff_map_int]

/-- Lower bound: if `U_μ ≥ m` at every root, `∫ log |Q| dμ ≥ μ(ℝ) log |lc Q| + deg Q · m`. -/
theorem le_integral_log_evalR_of_finite (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) {m : ℝ} (hm : ∀ ρ ∈ (Q.map (Int.castRingHom ℂ)).roots, m ≤ ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ) :
    μ.real univ * log |(Q.leadingCoeff : ℝ)| + Q.natDegree * m ≤
      ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ := by
  rw [integral_log_evalR_of_finite hlog hQ]
  have h := Multiset.sum_map_le_sum_map (s := (Q.map (Int.castRingHom ℂ)).roots) (fun _ => m) _ hm
  rw [Multiset.map_const', Multiset.sum_replicate, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_map_eq_of_injective (RingHom.injective_int _), nsmul_eq_mul] at h
  linarith

/-- Equality: if `U_μ = m` at every root, `∫ log |Q| dμ = μ(ℝ) log |lc Q| + deg Q · m`. -/
theorem integral_log_evalR_of_roots_of_finite (hlog : ∀ ρ : ℂ, Integrable (fun y : ℝ => log ‖ρ - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) {m : ℝ} (hm : ∀ ρ ∈ (Q.map (Int.castRingHom ℂ)).roots, ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ = m) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ = μ.real univ * log |(Q.leadingCoeff : ℝ)| + Q.natDegree * m := by
  rw [integral_log_evalR_of_finite hlog hQ, Multiset.map_congr rfl hm, Multiset.map_const', Multiset.sum_replicate,
    IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective (RingHom.injective_int _), nsmul_eq_mul]

end Poly

section Prob

/-! ## Probability measures: the forms used by the statements -/

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- **Root sum** (step 2 of Lemma U1): for a probability measure `μ` on `ℝ` without atoms with `log |z - y|`
`μ`-integrable for every `z`, and a nonzero `Q ∈ ℤ[X]`, `∫ log |Q| dμ = log |lc Q| + ∑_ρ U_μ(ρ)`. -/
theorem integral_log_evalR (hlog : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ =
      log |(Q.leadingCoeff : ℝ)| +
        ((Q.map (Int.castRingHom ℂ)).roots.map fun ρ => ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ).sum := by
  rw [integral_log_evalR_of_finite hlog hQ, probReal_univ, one_mul]

/-- If `U_μ ≥ m` at every root, `∫ log |Q| dμ ≥ log |lc Q| + deg Q · m`. -/
theorem le_integral_log_evalR (hlog : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) {m : ℝ} (hm : ∀ ρ ∈ (Q.map (Int.castRingHom ℂ)).roots, m ≤ ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ) :
    log |(Q.leadingCoeff : ℝ)| + Q.natDegree * m ≤ ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ := by
  have h := le_integral_log_evalR_of_finite hlog hQ hm
  rwa [probReal_univ, one_mul] at h

/-- If `U_μ = m` at every root, `∫ log |Q| dμ = log |lc Q| + deg Q · m`. -/
theorem integral_log_evalR_of_roots (hlog : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ)
    {Q : ℤ[X]} (hQ : Q ≠ 0) {m : ℝ} (hm : ∀ ρ ∈ (Q.map (Int.castRingHom ℂ)).roots, ∫ y, log ‖ρ - (y : ℂ)‖ ∂μ = m) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ = log |(Q.leadingCoeff : ℝ)| + Q.natDegree * m := by
  rw [integral_log_evalR_of_roots_of_finite hlog hQ hm, probReal_univ, one_mul]

end Prob

section Misc

/-! ## Atoms and integrability of continuous functions -/

/-- A measure with a density with respect to a measure without atoms has no atoms. -/
theorem nullSingletonClass_withDensity (μ : Measure ℝ) [NullSingletonClass μ] (f : ℝ → ENNReal) :
    NullSingletonClass (μ.withDensity f) :=
  ⟨fun x => withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

/-- A continuous function is integrable against a finite measure carried by `[a, b]`. -/
theorem integrable_of_continuous_of_compl_Icc {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : μ (Icc a b)ᶜ = 0) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ := by
  have h : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμ)
  rw [← h]
  exact hf.continuousOn.integrableOn_compact isCompact_Icc

end Misc

section Mix

/-! ## Mixtures `(1 - t) μ₀ + t ω` -/

variable {μ₀ ω : Measure ℝ} {t : ℝ}

theorem isProbabilityMeasure_mix [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ω] (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) := by
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) ht0, sub_add_cancel, ENNReal.ofReal_one]

theorem isFiniteMeasure_mix [IsFiniteMeasure μ₀] [IsFiniteMeasure ω] :
    IsFiniteMeasure (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) := by
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem mix_apply_eq_zero {s : Set ℝ} (h₀ : μ₀ s = 0) (hω : ω s = 0) :
    (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) s = 0 := by
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h₀, hω, smul_zero, smul_zero, add_zero]

theorem nullSingletonClass_mix [NullSingletonClass μ₀] [NullSingletonClass ω] :
    NullSingletonClass (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) :=
  ⟨fun x => mix_apply_eq_zero (measure_singleton x) (measure_singleton x)⟩

theorem integrable_mix {f : ℝ → ℝ} (h₀ : Integrable f μ₀) (hω : Integrable f ω) :
    Integrable f (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) :=
  (h₀.smul_measure ENNReal.ofReal_ne_top).add_measure (hω.smul_measure ENNReal.ofReal_ne_top)

theorem integral_mix {f : ℝ → ℝ} (h₀ : Integrable f μ₀) (hω : Integrable f ω) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ x, f x ∂(ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) =
      (1 - t) * ∫ x, f x ∂μ₀ + t * ∫ x, f x ∂ω := by
  rw [integral_add_measure (h₀.smul_measure ENNReal.ofReal_ne_top) (hω.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0,
    smul_eq_mul, smul_eq_mul]

theorem integrable_log_mix (h₀ : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ₀)
    (hω : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) ω) (z : ℂ) :
    Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) :=
  integrable_mix (h₀ z) (hω z)

theorem logPot_mix (h₀ : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ₀)
    (hω : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) ω) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℂ) :
    ∫ y, log ‖z - (y : ℂ)‖ ∂(ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) =
      (1 - t) * ∫ y, log ‖z - (y : ℂ)‖ ∂μ₀ + t * ∫ y, log ‖z - (y : ℂ)‖ ∂ω :=
  integral_mix (h₀ z) (hω z) ht0 ht1

end Mix

section MixPoly

variable {μ₀ ω : Measure ℝ} {t : ℝ}

theorem integrable_log_evalR_mix [IsFiniteMeasure μ₀] [NullSingletonClass μ₀] [IsFiniteMeasure ω]
    [NullSingletonClass ω] (h₀ : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ₀)
    (hω : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) ω) {Q : ℤ[X]} (hQ : Q ≠ 0) :
    Integrable (fun x => log |(Q.map (Int.castRingHom ℝ)).eval x|)
      (ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) :=
  integrable_mix (integrable_log_evalR h₀ hQ) (integrable_log_evalR hω hQ)

theorem integral_log_evalR_mix [IsFiniteMeasure μ₀] [NullSingletonClass μ₀] [IsFiniteMeasure ω]
    [NullSingletonClass ω] (h₀ : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ₀)
    (hω : ∀ z : ℂ, Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) ω) {Q : ℤ[X]} (hQ : Q ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂(ENNReal.ofReal (1 - t) • μ₀ + ENNReal.ofReal t • ω) =
      (1 - t) * ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂μ₀ +
        t * ∫ x, log |(Q.map (Int.castRingHom ℝ)).eval x| ∂ω :=
  integral_mix (integrable_log_evalR h₀ hQ) (integrable_log_evalR hω hQ) ht0 ht1

end MixPoly

end AuxCommon
