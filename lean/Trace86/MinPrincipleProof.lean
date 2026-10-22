import Trace86.Statement
import AuxCommon.Energy.MinPrinciple

/-!
# Proof of the named hypothesis `Trace86.MinPrinciple` (step 1 of Lemma U1 of the paper)

`theorem Trace86.minPrinciple : Trace86.MinPrinciple`.

With `U(z) = ∫ log |z - y| dμ(y)` and `h = U - ∑ wⱼ log |Qⱼ|`, put `S = [a, b] ⊆ ℂ`, `Z` the roots of the `Qⱼ` with
`wⱼ > 0`, and `Ω = ℂ \ (S ∪ Z)`. On `Ω` the function `h` is continuous and has the mean value property:
`U` by Fubini and Jensen's formula (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`) on discs missing `S`,
`log |Qⱼ|` by harmonicity on discs missing its roots. At the points of `Z`, `h → +∞`; at the points of `S \ Z`, `h` is
continuous and `≥ 0` (the hypothesis, extended by continuity to the roots of zero-weight `Qⱼ`); at infinity
`h ≥ (1 - ∑ wⱼ deg Qⱼ) log |z| - O(1) → +∞`. The minimum principle `AuxCommon.Energy.nonneg_of_superMean` gives
`h ≥ 0` on `Ω`, and on `S` minus the roots the hypothesis gives it.
-/

open Polynomial MeasureTheory Set Real Metric Filter
open scoped Topology
open AuxCommon AuxCommon.Energy

namespace Trace86

namespace MinPrin

lemma toC_eval_ofReal (Q : ℤ[X]) (x : ℝ) : (toC Q).eval (x : ℂ) = ((evalR Q x : ℝ) : ℂ) := by
  simp only [toC, evalR, Polynomial.eval_map]
  rw [← Complex.ofRealHom_eq_coe, ← Complex.ofRealHom_eq_coe, Polynomial.hom_eval₂]
  congr 1

lemma norm_toC_eval_ofReal (Q : ℤ[X]) (x : ℝ) : ‖(toC Q).eval (x : ℂ)‖ = |evalR Q x| := by
  rw [toC_eval_ofReal, Complex.norm_real, Real.norm_eq_abs]

lemma norm_ofReal_sub (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma toC_ne_zero {Q : ℤ[X]} (hQ : Q ≠ 0) : toC Q ≠ 0 :=
  Polynomial.map_ne_zero_iff (Int.cast_injective) |>.2 hQ

lemma natDegree_toC (Q : ℤ[X]) : (toC Q).natDegree = Q.natDegree :=
  Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q

lemma analyticAt_eval (p : ℂ[X]) (z : ℂ) : AnalyticAt ℂ (fun x => p.eval x) z :=
  (Polynomial.differentiable p).analyticAt z

lemma continuous_eval (p : ℂ[X]) : Continuous fun x : ℂ => p.eval x := Polynomial.continuous p

lemma circleIntegrable_log_norm_eval (p : ℂ[X]) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => log ‖p.eval z‖) c r :=
  MeromorphicOn.circleIntegrable_log_norm fun z _ => (analyticAt_eval p z).meromorphicAt

/-- Mean value property of `log |p|` on a closed disc free of roots of `p`. -/
lemma circleAverage_log_norm_eval {p : ℂ[X]} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hroot : ∀ z ∈ closedBall c r, p.eval z ≠ 0) :
    circleAverage (fun z => log ‖p.eval z‖) c r = log ‖p.eval c‖ := by
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  intro z hz
  rw [abs_of_pos hr] at hz
  exact (analyticAt_eval p z).harmonicAt_log_norm (hroot z hz)

/-- `|p(z)| ≤ C |z|^deg` for `|z| ≥ 1`, with `C = max 1 (∑ |coeffs|)`. -/
lemma norm_eval_le (p : ℂ[X]) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖p.eval z‖ ≤ max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖z‖ ^ p.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow]
        gcongr
        exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
        rw [Finset.sum_mul]
    _ ≤ max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
        gcongr
        exact le_max_right _ _

/-- `log |p(z)| ≤ log C + deg p · log |z|` for `|z| ≥ 1`. -/
lemma log_norm_eval_le (p : ℂ[X]) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    log ‖p.eval z‖ ≤ log (max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖)) +
      p.natDegree * log ‖z‖ := by
  set C := max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖)
  have hC : 1 ≤ C := le_max_left _ _
  have hz0 : 0 < ‖z‖ := by linarith
  have hlogz : 0 ≤ log ‖z‖ := log_nonneg hz
  rcases eq_or_ne (p.eval z) 0 with h0 | h0
  · rw [h0, norm_zero, log_zero]
    have := log_nonneg hC
    positivity
  · calc log ‖p.eval z‖ ≤ log (C * ‖z‖ ^ p.natDegree) :=
          log_le_log (norm_pos_iff.2 h0) (norm_eval_le p hz)
      _ = log C + p.natDegree * log ‖z‖ := by
          rw [log_mul (by positivity) (by positivity), log_pow]

/-- The potential `U(z) = ∫ log |z - y| dμ(y)` of a measure on `ℝ`. -/
noncomputable def U (μ : Measure ℝ) (z : ℂ) : ℝ := ∫ y, log ‖z - (y : ℂ)‖ ∂μ

/-- The segment `[a, b] ⊆ ℂ`. -/
def seg (a b : ℝ) : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc a b

lemma isCompact_seg (a b : ℝ) : IsCompact (seg a b) := isCompact_Icc.image Complex.continuous_ofReal

/-- Mean value property of `U` on a closed disc missing the segment (Fubini and Jensen's formula). -/
lemma circleAverage_U {a b : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc a b)ᶜ = 0)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hdisj : ∀ x ∈ Icc a b, r < ‖c - (x : ℂ)‖) :
    circleAverage (U μ) c r = U μ c := by
  have hmem : ∀ θ, circleMap c r θ ∈ sphere c r := fun θ => by simp [abs_of_pos hr]
  have hK : IsCompact (sphere c r ×ˢ seg a b) := (isCompact_sphere c r).prod (isCompact_seg a b)
  have hcontK : ContinuousOn (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) (sphere c r ×ˢ seg a b) := by
    intro p hp
    obtain ⟨hp1, x, hx, hpx⟩ := hp
    have hne : p.1 - p.2 ≠ 0 := by
      intro h0
      have h1 : p.1 = (x : ℂ) := (sub_eq_zero.1 h0).trans hpx.symm
      have h2 : ‖c - (x : ℂ)‖ = r := by rw [← h1, norm_sub_rev]; exact mem_sphere_iff_norm.1 hp1
      exact lt_irrefl r (h2 ▸ hdisj x hx)
    exact ((continuous_fst.sub continuous_snd).norm.continuousAt.log
      (norm_ne_zero_iff.2 hne)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcontK
  have hae : ∀ᵐ y ∂μ, y ∈ Icc a b := by rw [ae_iff]; exact hsupp
  have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (2 * π))) := isFiniteMeasure_restrict.2
    (by rw [uIoc_of_le two_pi_pos.le, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hFint : Integrable (Function.uncurry fun (θ y : ℝ) => log ‖circleMap c r θ - (y : ℂ)‖)
      ((volume.restrict (uIoc 0 (2 * π))).prod μ) := by
    refine Integrable.of_bound ?_ C ?_
    · have hcm : Continuous (circleMap c r) := continuous_circleMap c r
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · have hfull : ∀ᵐ p ∂((volume.restrict (uIoc 0 (2 * π))).prod μ), p.2 ∈ Icc a b := by
        rw [ae_iff]
        have : {p : ℝ × ℝ | ¬p.2 ∈ Icc a b} = univ ×ˢ (Icc a b)ᶜ := by ext p; simp
        rw [this, Measure.prod_prod, hsupp, mul_zero]
      filter_upwards [hfull] with p hp
      exact hC (circleMap c r p.1, (p.2 : ℂ)) ⟨hmem p.1, p.2, hp, rfl⟩
  rw [circleAverage_def, smul_eq_mul]
  simp only [U]
  rw [intervalIntegral_integral_swap hFint, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hae] with y hy
  have hJ := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (y : ℂ)) (c := c) hr.ne'
  rw [circleAverage_def, smul_eq_mul] at hJ
  rw [hJ]
  have hρ := hdisj y hy
  have hρ0 : 0 < ‖c - (y : ℂ)‖ := hr.trans hρ
  rw [posLog_eq_log (by rw [abs_of_pos (by positivity), le_inv_mul_iff₀ hr]; linarith),
    log_mul (inv_pos.2 hr).ne' hρ0.ne', log_inv]
  ring

variable {m : ℕ}

/-- `h(z) = U(z) - ∑ wⱼ log |Qⱼ(z)|`. -/
noncomputable def hfun (μ : Measure ℝ) (Q : Fin m → ℤ[X]) (w : Fin m → ℝ) (z : ℂ) : ℝ :=
  U μ z - ∑ j, w j * log ‖(toC (Q j)).eval z‖

/-- The roots of the `Qⱼ` with positive weight. -/
def posRoots (Q : Fin m → ℤ[X]) (w : Fin m → ℝ) : Set ℂ :=
  {z | ∃ j, 0 < w j ∧ (toC (Q j)).eval z = 0}

lemma posRoots_finite {Q : Fin m → ℤ[X]} (w : Fin m → ℝ) (hQ : ∀ j, Q j ≠ 0) : (posRoots Q w).Finite := by
  have : posRoots Q w ⊆ ⋃ j, {z | (toC (Q j)).IsRoot z} := by
    rintro z ⟨j, -, hj⟩
    exact mem_iUnion.2 ⟨j, hj⟩
  exact (Set.finite_iUnion fun j => Polynomial.finite_setOfPred_isRoot (toC_ne_zero (hQ j))).subset this

lemma continuousAt_hfun {μ : Measure ℝ} {Q : Fin m → ℤ[X]} {w : Fin m → ℝ} (hUc : Continuous (U μ))
    (hw : ∀ j, 0 ≤ w j) {z : ℂ} (hz : ∀ j, 0 < w j → (toC (Q j)).eval z ≠ 0) :
    ContinuousAt (hfun μ Q w) z := by
  unfold hfun
  refine hUc.continuousAt.sub ?_
  have : ∀ j ∈ (Finset.univ : Finset (Fin m)), ContinuousAt (fun z => w j * log ‖(toC (Q j)).eval z‖) z := by
    intro j _
    rcases (hw j).eq_or_lt with h0 | hpos
    · simp only [← h0, zero_mul]
      exact continuousAt_const
    · exact continuousAt_const.mul
        ((continuous_eval _).continuousAt.norm.log (norm_ne_zero_iff.2 (hz j hpos)))
  exact tendsto_finsetSum _ this

/-- Mean value property of `h` on closed discs in `Ω = ℂ \ (S ∪ Z)`. -/
lemma circleAverage_hfun {a b : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc a b)ᶜ = 0)
    (hUc : Continuous (U μ)) {Q : Fin m → ℤ[X]} {w : Fin m → ℝ} (hw : ∀ j, 0 ≤ w j) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall c r ⊆ (seg a b ∪ posRoots Q w)ᶜ) :
    circleAverage (hfun μ Q w) c r = hfun μ Q w c := by
  have hdisj : ∀ x ∈ Icc a b, r < ‖c - (x : ℂ)‖ := by
    intro x hx
    by_contra hle
    push Not at hle
    have hmem : (x : ℂ) ∈ closedBall c r := by
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hle
    exact hball hmem (Or.inl ⟨x, hx, rfl⟩)
  have hroot : ∀ j, 0 < w j → ∀ z ∈ closedBall c r, (toC (Q j)).eval z ≠ 0 := by
    intro j hj z hz h0
    exact hball hz (Or.inr ⟨j, hj, h0⟩)
  have hUci : CircleIntegrable (U μ) c r := hUc.continuousOn.circleIntegrable hr.le
  have hci : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      CircleIntegrable (fun z => w j * log ‖(toC (Q j)).eval z‖) c r :=
    fun j _ => (circleIntegrable_log_norm_eval _ c r).const_mul (w j)
  unfold hfun
  rw [circleAverage_fun_sub hUci (CircleIntegrable.fun_sum _ hci), circleAverage_U hsupp hr hdisj,
    circleAverage_fun_sum hci]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsm : circleAverage (fun z => w j * log ‖(toC (Q j)).eval z‖) c r =
      w j * circleAverage (fun z => log ‖(toC (Q j)).eval z‖) c r := by
    rw [← smul_eq_mul, ← circleAverage_fun_smul]
    rfl
  rw [hsm]
  rcases (hw j).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · rw [circleAverage_log_norm_eval hr (hroot j hpos)]

/-- Near a root `ζ` of a positive-weight `Qⱼ₀`, `h → +∞`. -/
lemma eventually_lt_hfun_root {μ : Measure ℝ} {Q : Fin m → ℤ[X]} {w : Fin m → ℝ} (hUc : Continuous (U μ))
    (hw : ∀ j, 0 ≤ w j) {ζ : ℂ} {j0 : Fin m} (hj0 : 0 < w j0) (hζ : (toC (Q j0)).eval ζ = 0) (c0 : ℝ) :
    ∀ᶠ z in 𝓝 ζ, (toC (Q j0)).eval z ≠ 0 → c0 < hfun μ Q w z := by
  set L : Fin m → ℝ := fun j => log (‖(toC (Q j)).eval ζ‖ + 1) with hL
  have hL0 : ∀ j, 0 ≤ L j := fun j => log_nonneg (by linarith [norm_nonneg ((toC (Q j)).eval ζ)])
  have hev1 : ∀ᶠ z in 𝓝 ζ, ∀ j, log ‖(toC (Q j)).eval z‖ ≤ L j := by
    rw [Filter.eventually_all]
    intro j
    have hc := ((continuous_eval (toC (Q j))).norm.continuousAt (x := ζ))
    filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one _))] with z hz
    rcases eq_or_ne ((toC (Q j)).eval z) 0 with h0 | h0
    · rw [h0, norm_zero, log_zero]; exact hL0 j
    · exact log_le_log (norm_pos_iff.2 h0) hz.le
  have hev2 : ∀ᶠ z in 𝓝 ζ, U μ ζ - 1 < U μ z :=
    hUc.continuousAt.eventually (lt_mem_nhds (by linarith))
  set M : ℝ := (|c0| + |U μ ζ| + 1 + ∑ j, w j * L j) / w j0 + 1 with hM
  have hev3 : ∀ᶠ z in 𝓝 ζ, ‖(toC (Q j0)).eval z‖ < exp (-M) := by
    have hc := ((continuous_eval (toC (Q j0))).norm.continuousAt (x := ζ))
    rw [ContinuousAt, hζ, norm_zero] at hc
    exact hc.eventually (gt_mem_nhds (exp_pos _))
  filter_upwards [hev1, hev2, hev3] with z h1 h2 h3 hz0
  have h4 : log ‖(toC (Q j0)).eval z‖ < -M := by
    rw [← log_exp (-M)]
    exact log_lt_log (norm_pos_iff.2 hz0) h3
  have h5 : w j0 * (L j0 - log ‖(toC (Q j0)).eval z‖) ≤
      ∑ j, w j * (L j - log ‖(toC (Q j)).eval z‖) :=
    Finset.single_le_sum (f := fun j => w j * (L j - log ‖(toC (Q j)).eval z‖))
      (fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (h1 j))) (Finset.mem_univ j0)
  have h6 : ∑ j, w j * (L j - log ‖(toC (Q j)).eval z‖) =
      ∑ j, w j * L j - ∑ j, w j * log ‖(toC (Q j)).eval z‖ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsumL : 0 ≤ ∑ j, w j * L j := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hL0 j)
  have h7 : w j0 * M ≤ w j0 * (-log ‖(toC (Q j0)).eval z‖) :=
    mul_le_mul_of_nonneg_left (by linarith) hj0.le
  have h8 : w j0 * M = |c0| + |U μ ζ| + 1 + ∑ j, w j * L j + w j0 := by
    rw [hM]
    field_simp
  unfold hfun
  linarith [mul_nonneg hj0.le (hL0 j0), le_abs_self c0, neg_abs_le (U μ ζ)]

/-- At a point `x` of `[a, b]` that is not a root of a positive-weight `Qⱼ`, `h(x) ≥ 0`: the hypothesis gives it
off the (finitely many) real roots of all `Qⱼ`, and `h` is continuous at `x`. -/
lemma hfun_nonneg_seg {a b : ℝ} (hab : a < b) {μ : Measure ℝ} (hUc : Continuous (U μ)) {Q : Fin m → ℤ[X]}
    {w : Fin m → ℝ} (hw : ∀ j, 0 ≤ w j) (hQ : ∀ j, Q j ≠ 0)
    (hpos : ∀ x : ℝ, a ≤ x → x ≤ b → (∀ j, evalR (Q j) x ≠ 0) →
      0 ≤ (∫ y, Real.log |x - y| ∂μ) - ∑ j, w j * Real.log |evalR (Q j) x|)
    {x : ℝ} (hx : x ∈ Icc a b) (hxz : ∀ j, 0 < w j → (toC (Q j)).eval (x : ℂ) ≠ 0) :
    0 ≤ hfun μ Q w x := by
  set F : Set ℝ := ⋃ j, {t : ℝ | (Q j).map (Int.castRingHom ℝ) |>.IsRoot t} with hF
  have hFfin : F.Finite :=
    Set.finite_iUnion fun j => Polynomial.finite_setOfPred_isRoot
      ((Polynomial.map_ne_zero_iff Int.cast_injective).2 (hQ j))
  have hφ : ∀ t ∈ Icc a b \ F, 0 ≤ hfun μ Q w (t : ℂ) := by
    rintro t ⟨ht, htF⟩
    have hnz : ∀ j, evalR (Q j) t ≠ 0 := fun j h0 => htF (mem_iUnion.2 ⟨j, h0⟩)
    have := hpos t ht.1 ht.2 hnz
    unfold hfun U
    simp only [norm_ofReal_sub, norm_toC_eval_ofReal]
    exact this
  have hcl : x ∈ closure (Icc a b \ F) := by
    have hdense : Dense Fᶜ := hFfin.countable.dense_compl ℝ
    have h1 : Ioo a b ⊆ closure (Ioo a b ∩ Fᶜ) := hdense.open_subset_closure_inter isOpen_Ioo
    have h2 : closure (Ioo a b) ⊆ closure (Ioo a b ∩ Fᶜ) := closure_minimal h1 isClosed_closure
    rw [closure_Ioo hab.ne] at h2
    have h3 : Ioo a b ∩ Fᶜ ⊆ Icc a b \ F := fun t ht => ⟨Ioo_subset_Icc_self ht.1, ht.2⟩
    exact closure_mono h3 (h2 hx)
  have hcont : ContinuousAt (fun t : ℝ => hfun μ Q w (t : ℂ)) x :=
    (continuousAt_hfun hUc hw hxz).comp Complex.continuous_ofReal.continuousAt
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hφ)

/-- At infinity, `h(z) ≥ (1 - β) log |z| - log 2 - A > 0` with `β = ∑ wⱼ deg Qⱼ < 1`. -/
lemma exists_pos_hfun {a b : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc a b)ᶜ = 0)
    {Q : Fin m → ℤ[X]} {w : Fin m → ℝ} (hw : ∀ j, 0 ≤ w j) (hdeg : ∑ j, w j * (Q j).natDegree < 1) :
    ∃ R, ∀ z : ℂ, R < ‖z‖ → 0 < hfun μ Q w z := by
  set R0 := |a| + |b| with hR0
  set C : Fin m → ℝ := fun j =>
    max 1 (∑ i ∈ Finset.range ((toC (Q j)).natDegree + 1), ‖(toC (Q j)).coeff i‖) with hC
  set A := ∑ j, w j * log (C j) with hA
  set β := ∑ j, w j * ((Q j).natDegree : ℝ) with hβ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (log_nonneg (le_max_left _ _))
  refine ⟨max (2 * R0 + 2) (exp ((log 2 + A) / (1 - β))), fun z hz => ?_⟩
  have hz1 : 2 * R0 + 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : exp ((log 2 + A) / (1 - β)) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have hR00 : 0 ≤ R0 := by positivity
  have hz1' : 1 ≤ ‖z‖ := by linarith
  have hae : ∀ᵐ y ∂μ, y ∈ Icc a b := by rw [ae_iff]; exact hsupp
  have hlow : ∀ y ∈ Icc a b, ‖z‖ / 2 ≤ ‖z - (y : ℂ)‖ ∧ ‖z - (y : ℂ)‖ ≤ ‖z‖ + R0 := by
    intro y hy
    have hy0 : |y| ≤ R0 := by
      have := abs_le_max_abs_abs hy.1 hy.2
      linarith [max_le_add_of_nonneg (abs_nonneg a) (abs_nonneg b)]
    have h1 := norm_sub_norm_le z (y : ℂ)
    have h2 := norm_sub_le z (y : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1 h2
    constructor <;> linarith
  have hU : log ‖z‖ - log 2 ≤ U μ z := by
    have hint : Integrable (fun y : ℝ => log ‖z - (y : ℂ)‖) μ := by
      refine Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop))
        (|log (‖z‖ / 2)| + |log (‖z‖ + R0)|) ?_
      filter_upwards [hae] with y hy
      obtain ⟨h1, h2⟩ := hlow y hy
      have hl1 := log_le_log (by positivity) h1
      have hl2 := log_le_log (by linarith) h2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [neg_abs_le (log (‖z‖ / 2)), abs_nonneg (log (‖z‖ + R0)),
        le_abs_self (log (‖z‖ + R0)), abs_nonneg (log (‖z‖ / 2))]
    calc log ‖z‖ - log 2 = ∫ _y, (log ‖z‖ - log 2) ∂μ := by
          rw [integral_const, probReal_univ, one_smul]
      _ ≤ ∫ y, log ‖z - (y : ℂ)‖ ∂μ := by
          refine integral_mono_ae (integrable_const _) hint ?_
          filter_upwards [hae] with y hy
          rw [← log_div (by linarith) two_ne_zero]
          exact log_le_log (by positivity) (hlow y hy).1
  have hQb : ∑ j, w j * log ‖(toC (Q j)).eval z‖ ≤ A + β * log ‖z‖ := by
    have hj : ∀ j, w j * log ‖(toC (Q j)).eval z‖ ≤
        w j * log (C j) + w j * ((Q j).natDegree : ℝ) * log ‖z‖ := by
      intro j
      have h := log_norm_eval_le (toC (Q j)) hz1'
      have hd : ((toC (Q j)).natDegree : ℝ) = (Q j).natDegree := by rw [natDegree_toC]
      rw [hd] at h
      have := mul_le_mul_of_nonneg_left h (hw j)
      simp only [hC]
      linarith
    calc ∑ j, w j * log ‖(toC (Q j)).eval z‖
        ≤ ∑ j, (w j * log (C j) + w j * ((Q j).natDegree : ℝ) * log ‖z‖) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = A + β * log ‖z‖ := by rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hlog : (log 2 + A) / (1 - β) < log ‖z‖ := by
    rw [← log_exp ((log 2 + A) / (1 - β))]
    exact log_lt_log (exp_pos _) hz2
  have hβ1 : 0 < 1 - β := by linarith
  have h3 : log 2 + A < (1 - β) * log ‖z‖ := by
    rw [div_lt_iff₀ hβ1] at hlog
    linarith
  unfold hfun
  nlinarith

end MinPrin

open MinPrin in
/-- **The named hypothesis `MinPrinciple` holds** (minimum principle, step 1 of Lemma U1 of the paper). -/
theorem minPrinciple : MinPrinciple := by
  intro a b hab μ hμ hsupp hUc m Q w hQ hw hdeg hpos z hz
  have hUc' : Continuous (U μ) := hUc
  have hclosed : IsClosed (seg a b ∪ posRoots Q w) :=
    (isCompact_seg a b).isClosed.union (posRoots_finite w hQ).isClosed
  by_cases hzS : z ∈ seg a b
  · obtain ⟨x, hx, rfl⟩ := hzS
    have hnz : ∀ j, evalR (Q j) x ≠ 0 := fun j h0 =>
      hz j (by rw [toC_eval_ofReal, h0, Complex.ofReal_zero])
    have := hpos x hx.1 hx.2 hnz
    simp only [norm_ofReal_sub, norm_toC_eval_ofReal]
    exact this
  · have hzΩ : z ∈ (seg a b ∪ posRoots Q w)ᶜ := by
      rintro (h | ⟨j, -, hj⟩)
      · exact hzS h
      · exact hz j hj
    refine nonneg_of_superMean (h := hfun μ Q w) hclosed.isOpen_compl ?_ ?_ ?_ ?_ ?_ z hzΩ
    · exact ⟨(a : ℂ), by rw [compl_compl]; exact Or.inl ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩⟩
    · intro z' hz'
      refine (continuousAt_hfun hUc' hw fun j hj h0 => hz' (Or.inr ⟨j, hj, h0⟩)).continuousWithinAt
    · intro c r hr hball
      exact (circleAverage_hfun hsupp hUc' hw hr hball).le
    · intro ζ hζ c0 hc0
      rw [notMem_compl_iff] at hζ
      by_cases hζZ : ζ ∈ posRoots Q w
      · obtain ⟨j0, hj0, hζ0⟩ := hζZ
        filter_upwards [eventually_lt_hfun_root hUc' hw hj0 hζ0 c0] with z' hz' hz'Ω
        exact hz' fun h0 => hz'Ω (Or.inr ⟨j0, hj0, h0⟩)
      · have hζS : ζ ∈ seg a b := hζ.resolve_right hζZ
        obtain ⟨x, hx, rfl⟩ := hζS
        have hxz : ∀ j, 0 < w j → (toC (Q j)).eval (x : ℂ) ≠ 0 := fun j hj h0 => hζZ ⟨j, hj, h0⟩
        have h0 := hfun_nonneg_seg hab hUc' hw hQ hpos hx hxz
        have hc := continuousAt_hfun hUc' hw hxz
        filter_upwards [hc.eventually (lt_mem_nhds (show hfun μ Q w x + c0 < hfun μ Q w x by linarith))]
          with z' hz' _
        linarith
    · intro c0 hc0
      obtain ⟨R, hR⟩ := exists_pos_hfun hsupp hw hdeg
      exact ⟨R, fun z' _ hz' => hc0.trans (hR z' hz')⟩

end Trace86
