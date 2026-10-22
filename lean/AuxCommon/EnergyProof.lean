import AuxCommon.Energy.Nu

/-!
# Proof of the named hypothesis `AuxCommon.EnergySmoothing`

`theorem AuxCommon.energySmoothing : AuxCommon.EnergySmoothing`.

Proof (paper, Lemma 2.1 and the steps "Smoothing" and "Energy" of Lemma 2.2): let `σ_i` be the normalized arc-length
measure on the circle `|z - α_i| = r` and `τ = (1/n) Σ σ_i`. With `Λ(μ, μ') = ∫∫ (log D - log |z - w|) dμ'(w) dμ(z)`
(`D` larger than the diameter of all supports):
* `Λ(σ_i, σ_i) = log D - log r` and `Λ(σ_i, σ_k) ≤ log D - log |α_i - α_k|` for `i ≠ k` (Jensen's formula);
* `Λ(σ_i, ν) ≥ log D - U_ν(α_i) - K r` (Jensen's formula and the layer-cake bound from `DiscBound`);
* `Λ(ν, ν) = log D - I(ν)`;
* `2 Λ(τ, ν) ≤ Λ(τ, τ) + Λ(ν, ν)` (`two_mul_Lam_le`: Frullani + positive definiteness of the Gaussian kernel).
-/

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal

namespace AuxCommon

namespace Energy

/-- A finite measure with the disc bound has no atoms. -/
lemma measure_singleton_of_discBound {ν : Measure ℂ} [IsFiniteMeasure ν] {K : ℝ} (hK : 0 < K)
    (hdisc : DiscBound ν K) (z : ℂ) : ν {z} = 0 := by
  have h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (ν {z}).toReal ≤ K * ε := fun ε hε hε1 =>
    (ENNReal.toReal_mono (measure_ne_top ν _)
      (measure_mono (singleton_subset_iff.2 (mem_ball_self hε)))).trans (hdisc z ε hε hε1)
  have h0 : (ν {z}).toReal ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 := h (min 1 ((ν {z}).toReal / (2 * K))) (lt_min one_pos (by positivity)) (min_le_left _ _)
    have h2 : K * min 1 ((ν {z}).toReal / (2 * K)) ≤ (ν {z}).toReal / 2 := by
      calc K * min 1 ((ν {z}).toReal / (2 * K)) ≤ K * ((ν {z}).toReal / (2 * K)) := by
            gcongr; exact min_le_right _ _
        _ = (ν {z}).toReal / 2 := by field_simp
    linarith
  rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
  · exact h
  · exact absurd h (measure_ne_top ν _)

lemma measurable_ofReal_Lk_sub (D : ℝ) : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (Lk D (p.1 - p.2)) := by
  unfold Lk; fun_prop

lemma Lam_smul_sum_left (D : ℝ) (c : ℝ≥0∞) {n : ℕ} (μs : Fin n → Measure ℂ) (μ' : Measure ℂ) :
    Lam D (c • ∑ i, μs i) μ' = c * ∑ i, Lam D (μs i) μ' := by
  unfold Lam
  rw [lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]

lemma Lam_smul_sum_right (D : ℝ) {c : ℝ≥0∞} (hc : c ≠ ⊤) {n : ℕ} (μ : Measure ℂ) (μs : Fin n → Measure ℂ)
    [∀ i, SFinite (μs i)] :
    Lam D μ (c • ∑ i, μs i) = c * ∑ i, Lam D μ (μs i) := by
  unfold Lam
  simp_rw [lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hc, lintegral_finsetSum]
  intro i _
  exact (measurable_ofReal_Lk_sub D).lintegral_prod_right'

end Energy

open Energy

/-- **The named hypothesis `EnergySmoothing` holds** (Saff-Totik, Lemma I.1.8, and Jensen's formula). -/
theorem energySmoothing : EnergySmoothing := by
  intro ν hν K hK hcs hdisc n α hn hα r hr hr1
  obtain ⟨R, hR⟩ := hcs
  -- the kernel constant `D = 2 R₀`, with all supports in `closedBall 0 R₀`
  have hsum : 0 ≤ ∑ i, ‖α i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 2 * (1 + |R| + ∑ i, ‖α i‖) := ⟨_, rfl⟩
  have hD : 1 ≤ D := by rw [hDdef]; linarith [abs_nonneg R]
  have hD0 : 0 < D := by linarith
  have hαD : ∀ i, ‖α i‖ + r ≤ D / 2 := by
    intro i
    have := Finset.single_le_sum (f := fun i => ‖α i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
    rw [hDdef]
    linarith [abs_nonneg R]
  -- the reference measure: support and atoms
  have hνsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ D / 2 := by
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hR
    simp only [mem_ofPred_eq, not_le] at hy
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
    rw [hDdef] at hy
    linarith [le_abs_self R]
  have hνat : ∀ z, ν {z} = 0 := measure_singleton_of_discBound hK hdisc
  -- the circle measures and their average `τ`
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hnit : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hn0
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin n → Measure ℂ, σ = fun i => circleMeasure (α i) r := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Measure ℂ, τ = (n : ℝ≥0∞)⁻¹ • ∑ i, σ i := ⟨_, rfl⟩
  have : ∀ i, IsProbabilityMeasure (σ i) := fun i => by rw [hσ]; infer_instance
  have : IsProbabilityMeasure τ := by
    constructor
    rw [hτ, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hn0 hnt
  have hτsupp : ∀ᵐ z ∂τ, ‖z‖ ≤ D / 2 := by
    rw [ae_iff, hτ, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    have : ∀ i, σ i {a | ¬‖a‖ ≤ D / 2} = 0 := fun i => by
      rw [hσ]; exact ae_iff.1 (circleMeasure_ae_norm_le hr (hαD i))
    rw [Finset.sum_eq_zero fun i _ => this i, smul_zero]
  have hτat : ∀ z, τ {z} = 0 := by
    intro z
    rw [hτ, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp [hσ, circleMeasure_singleton _ hr.ne']
  -- the energy inequality `2 Λ(τ, ν) ≤ Λ(τ, τ) + Λ(ν, ν)`
  have hE := two_mul_Lam_le hD0 τ ν hτsupp hνsupp hτat hνat
  have hLτν : Lam D τ ν = (n : ℝ≥0∞)⁻¹ * ∑ i, Lam D (σ i) ν := by
    rw [hτ, Lam_smul_sum_left]
  have hLττ : Lam D τ τ = (n : ℝ≥0∞)⁻¹ * ∑ i, ((n : ℝ≥0∞)⁻¹ * ∑ k, Lam D (σ i) (σ k)) := by
    conv_lhs => rw [hτ, Lam_smul_sum_left, ← hτ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hτ, Lam_smul_sum_right D hnit]
  -- the three kinds of terms
  have hself : ∀ i, Lam D (σ i) (σ i) = ENNReal.ofReal (log D - log r) := fun i => by
    rw [hσ]; exact Lam_circle_self hD (α i) hr (hαD i)
  have hcross : ∀ i k, i ≠ k → Lam D (σ i) (σ k) ≤ ENNReal.ofReal (log D - log ‖α i - α k‖) :=
    fun i k hik => by
      rw [hσ]; exact Lam_circle_circle_le hD (hα.ne hik) hr (hαD i) (hαD k)
  have hsmooth : ∀ i, ENNReal.ofReal (log D - logPot ν (α i)) ≤ Lam D (σ i) ν + ENNReal.ofReal (K * r) ∧
      Lam D (σ i) ν ≤ ENNReal.ofReal (log D - logPot ν (α i)) := fun i => by
    have h1 := Lam_circle_nu_add hK.le hdisc hD hνsupp hνat hr hr1 (hαD i)
    have h2 := lintegral_posLog_div_le hK.le hdisc (α i) hr hr1
    rw [hσ]
    constructor
    · rw [← h1]; gcongr
    · rw [← h1]; exact le_self_add
  have hνν := Lam_nu_nu hK.le hdisc hD hνsupp
  -- finiteness
  have hfin_ik : ∀ i k, Lam D (σ i) (σ k) ≠ ⊤ := fun i k => by
    rcases eq_or_ne i k with rfl | hik
    · rw [hself]; exact ENNReal.ofReal_ne_top
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcross i k hik)
  have hfin_iν : ∀ i, Lam D (σ i) ν ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsmooth i).2
  have hfin_νν : Lam D ν ν ≠ ⊤ := by rw [hνν]; exact ENNReal.ofReal_ne_top
  have hfin_ττ : Lam D τ τ ≠ ⊤ := by
    rw [hLττ]
    exact ENNReal.mul_ne_top hnit (ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.mul_ne_top hnit (ENNReal.sum_ne_top.2 fun k _ => hfin_ik i k))
  -- pass to real numbers
  set N : ℝ := (n : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hn
  have hreal : 2 * (Lam D τ ν).toReal ≤ (Lam D τ τ).toReal + (Lam D ν ν).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin_ττ, hfin_νν⟩) hE
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hfin_ττ hfin_νν, ENNReal.toReal_ofNat] at this
  have hτνr : (Lam D τ ν).toReal = N⁻¹ * ∑ i, (Lam D (σ i) ν).toReal := by
    rw [hLτν, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun i _ => hfin_iν i]
  have hττr : (Lam D τ τ).toReal = N⁻¹ * ∑ i, (N⁻¹ * ∑ k, (Lam D (σ i) (σ k)).toReal) := by
    rw [hLττ, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top hnit (ENNReal.sum_ne_top.2 fun k _ => hfin_ik i k)]
    refine congrArg (N⁻¹ * ·) (Finset.sum_congr rfl fun i _ => ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun k _ => hfin_ik i k]
  have hννr : (Lam D ν ν).toReal = log D - logEnergy ν := by
    rw [hνν, ENNReal.toReal_ofReal (sub_nonneg.2 (logEnergy_le hK.le hdisc hD hνsupp))]
  -- real bounds for the terms
  have hself_r : ∀ i, (Lam D (σ i) (σ i)).toReal = log D - log r := fun i => by
    rw [hself, ENNReal.toReal_ofReal (by linarith [log_nonpos hr.le hr1, log_nonneg hD])]
  have hcross_r : ∀ i k, i ≠ k → (Lam D (σ i) (σ k)).toReal ≤ log D - log ‖α i - α k‖ := by
    intro i k hik
    have hle : ‖α i - α k‖ ≤ D := (norm_sub_le _ _).trans (by linarith [hαD i, hαD k])
    have hpos : 0 < ‖α i - α k‖ := norm_pos_iff.2 (sub_ne_zero.2 (hα.ne hik))
    have h0 : 0 ≤ log D - log ‖α i - α k‖ := by linarith [log_le_log hpos hle]
    calc (Lam D (σ i) (σ k)).toReal ≤ (ENNReal.ofReal (log D - log ‖α i - α k‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcross i k hik)
      _ = log D - log ‖α i - α k‖ := ENNReal.toReal_ofReal h0
  have hsmooth_r : ∀ i, log D - logPot ν (α i) - K * r ≤ (Lam D (σ i) ν).toReal := by
    intro i
    have h0 : 0 ≤ log D - logPot ν (α i) := by
      linarith [(logPot_bounds hK.le hdisc hD hνsupp (show ‖α i‖ ≤ D / 2 by linarith [hαD i])).2]
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin_iν i, ENNReal.ofReal_ne_top⟩) (hsmooth i).1
    rw [ENNReal.toReal_ofReal h0, ENNReal.toReal_add (hfin_iν i) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  -- sums
  have hcard : ∀ i : Fin n, ((Finset.univ.erase i).card : ℝ) = N - 1 := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hn, Nat.cast_one]
  have hrow : ∀ i, ∑ k, (Lam D (σ i) (σ k)).toReal ≤
      N * log D - log r - ∑ k ∈ Finset.univ.erase i, log ‖α i - α k‖ := by
    intro i
    calc ∑ k, (Lam D (σ i) (σ k)).toReal
        = (Lam D (σ i) (σ i)).toReal + ∑ k ∈ Finset.univ.erase i, (Lam D (σ i) (σ k)).toReal :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      _ ≤ (log D - log r) + ∑ k ∈ Finset.univ.erase i, (log D - log ‖α i - α k‖) := by
          rw [hself_r]
          gcongr with k hk
          exact hcross_r i k (Finset.ne_of_mem_erase hk).symm
      _ = N * log D - log r - ∑ k ∈ Finset.univ.erase i, log ‖α i - α k‖ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
          ring
  set S := ∑ i, ∑ k ∈ Finset.univ.erase i, log ‖α i - α k‖ with hS
  set SU := ∑ i, logPot ν (α i) with hSU
  have hA : (Lam D τ τ).toReal ≤ log D - N⁻¹ * log r - N⁻¹ * N⁻¹ * S := by
    rw [hττr]
    calc N⁻¹ * ∑ i, (N⁻¹ * ∑ k, (Lam D (σ i) (σ k)).toReal)
        ≤ N⁻¹ * ∑ i, (N⁻¹ * (N * log D - log r - ∑ k ∈ Finset.univ.erase i, log ‖α i - α k‖)) := by
          gcongr with i
          exact hrow i
      _ = log D - N⁻¹ * log r - N⁻¹ * N⁻¹ * S := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          field_simp
          ring
  have hB : log D - N⁻¹ * SU - K * r ≤ (Lam D τ ν).toReal := by
    rw [hτνr]
    calc log D - N⁻¹ * SU - K * r = N⁻¹ * ∑ i, (log D - logPot ν (α i) - K * r) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          field_simp
          ring
      _ ≤ N⁻¹ * ∑ i, (Lam D (σ i) ν).toReal := by
          gcongr with i
          exact hsmooth_r i
  -- conclusion
  have hgoalL : 1 / N ^ 2 * S + log r / N - 2 * K * r = N⁻¹ * N⁻¹ * S + N⁻¹ * log r - 2 * K * r := by
    ring
  have hgoalR : 1 / N * ∑ i, (2 * logPot ν (α i) - logEnergy ν) = 2 * (N⁻¹ * SU) - logEnergy ν := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    rw [hSU, hN]
  rw [hgoalL, hgoalR]
  linarith [hreal, hA, hB, hννr]

end AuxCommon
