import Mathlib

/-!
# A minimum principle for functions with the super-mean-value property

`nonneg_of_superMean`: let `Ω ⊆ ℂ` be open with nonempty complement and `h : ℂ → ℝ` continuous on `Ω` with
`circleAverage h c r ≤ h c` for every closed disc `closedBall c r ⊆ Ω` (`r > 0`). If `liminf h ≥ 0` at every point of
the complement (approached from `Ω`) and at infinity, then `h ≥ 0` on `Ω`.

Proof: if `h z₀ < 0`, the minimum of `h` over `Ω` is attained (on a compact set, by the two `liminf` conditions) at
some `z₁`; the largest open disc around `z₁` inside `Ω` touches the complement at `ζ`, and by the strict positivity of
circle averages (`lt_circleAverage_of_ge`) `h` equals its minimum on that disc, contradicting `liminf h ≥ 0` at `ζ`.
-/

open MeasureTheory Set Real Metric Filter
open scoped Topology

namespace AuxCommon.Energy

/-- If `h` is continuous on the circle `|z - c| = r` (`r > 0`), `h ≥ m` there and `h z > m` at one of its points, then
the circle average of `h` exceeds `m`. -/
lemma lt_circleAverage_of_ge {h : ℂ → ℝ} {c : ℂ} {r m : ℝ} (hr : 0 < r) (hcont : ContinuousOn h (sphere c r))
    (hge : ∀ z ∈ sphere c r, m ≤ h z) {z : ℂ} (hz : z ∈ sphere c r) (hzm : m < h z) :
    m < circleAverage h c r := by
  have hmem : ∀ θ, circleMap c r θ ∈ sphere c r := fun θ => by
    simp [abs_of_pos hr]
  set g : ℝ → ℝ := fun θ => h (circleMap c r θ) - m with hg
  have hgc : Continuous g :=
    (hcont.comp_continuous (continuous_circleMap c r) hmem).sub continuous_const
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => sub_nonneg.2 (hge _ (hmem θ))
  obtain ⟨θ0, hθ0⟩ : z ∈ range (circleMap c r) := by rw [range_circleMap, abs_of_pos hr]; exact hz
  have hgθ0 : 0 < g θ0 := by simp only [hg, hθ0]; linarith
  have hper : Function.Periodic g (2 * π) := fun θ => by simp only [hg, periodic_circleMap c r θ]
  have hint : 0 < ∫ θ in (θ0 - π)..(θ0 - π) + 2 * π, g θ := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hg0)
      (hgc.intervalIntegrable _ _)]
    refine ⟨by linarith [pi_pos], ?_⟩
    have hopen : IsOpen (Function.support g ∩ Ioo (θ0 - π) (θ0 - π + 2 * π)) :=
      (isOpen_ne_fun hgc continuous_const).inter isOpen_Ioo
    have hθ : θ0 ∈ Function.support g ∩ Ioo (θ0 - π) (θ0 - π + 2 * π) :=
      ⟨hgθ0.ne', by constructor <;> linarith [pi_pos]⟩
    calc (0 : ENNReal) < volume (Function.support g ∩ Ioo (θ0 - π) (θ0 - π + 2 * π)) :=
          hopen.measure_pos volume ⟨θ0, hθ⟩
      _ ≤ volume (Function.support g ∩ Ioc (θ0 - π) (θ0 - π + 2 * π)) :=
          measure_mono (inter_subset_inter_right _ Ioo_subset_Ioc_self)
  have h0 : ∫ θ in (0 : ℝ)..2 * π, g θ = ∫ θ in (θ0 - π)..(θ0 - π) + 2 * π, g θ := by
    simpa using hper.intervalIntegral_add_eq 0 (θ0 - π)
  have hca : circleAverage h c r = (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, g θ) + m := by
    have hhc : Continuous fun θ => h (circleMap c r θ) := hcont.comp_continuous (continuous_circleMap c r) hmem
    have hI : ∫ θ in (0 : ℝ)..2 * π, g θ = (∫ θ in (0 : ℝ)..2 * π, h (circleMap c r θ)) - 2 * π * m := by
      simp only [hg]
      rw [intervalIntegral.integral_sub (hhc.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [hI, circleAverage_def, smul_eq_mul]
    field_simp
    ring
  rw [hca, h0]
  have : 0 < (2 * π)⁻¹ * ∫ θ in (θ0 - π)..(θ0 - π) + 2 * π, g θ := mul_pos (by positivity) hint
  linarith

/-- **Minimum principle** for continuous functions with the super-mean-value property on an open set `Ω ⊆ ℂ` with
nonempty complement, given `liminf h ≥ 0` at the complement and at infinity. -/
theorem nonneg_of_superMean {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ωᶜ.Nonempty) {h : ℂ → ℝ}
    (hcont : ContinuousOn h Ω)
    (hmean : ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ Ω → circleAverage h c r ≤ h c)
    (hbd : ∀ ζ ∉ Ω, ∀ c0 : ℝ, c0 < 0 → ∀ᶠ z in 𝓝 ζ, z ∈ Ω → c0 < h z)
    (hinf : ∀ c0 : ℝ, c0 < 0 → ∃ R, ∀ z ∈ Ω, R < ‖z‖ → c0 < h z) :
    ∀ z ∈ Ω, 0 ≤ h z := by
  intro z0 hz0
  by_contra hneg
  push Not at hneg
  set c0 := h z0 with hc0
  -- open neighborhoods of the points of the complement on which `h > c0`
  have hV : ∀ ζ : (Ωᶜ : Set ℂ), ∃ V : Set ℂ, IsOpen V ∧ (ζ : ℂ) ∈ V ∧ ∀ z ∈ V, z ∈ Ω → c0 < h z := by
    intro ζ
    obtain ⟨t, ht, hto, hζt⟩ := _root_.eventually_nhds_iff.1 (hbd ζ ζ.2 c0 hneg)
    exact ⟨t, hto, hζt, ht⟩
  choose V hVo hVmem hVh using hV
  have hWo : IsOpen (⋃ ζ : (Ωᶜ : Set ℂ), V ζ) := isOpen_iUnion hVo
  have hcW : Ωᶜ ⊆ ⋃ ζ : (Ωᶜ : Set ℂ), V ζ := fun ζ hζ => mem_iUnion.2 ⟨⟨ζ, hζ⟩, hVmem _⟩
  have hWh : ∀ z ∈ ⋃ ζ : (Ωᶜ : Set ℂ), V ζ, z ∈ Ω → c0 < h z := by
    intro z hz hzΩ
    obtain ⟨ζ, hζ⟩ := mem_iUnion.1 hz
    exact hVh ζ z hζ hzΩ
  obtain ⟨R, hR⟩ := hinf c0 hneg
  -- the compact set `T` on which the minimum is attained
  set T := closedBall (0 : ℂ) R ∩ (⋃ ζ : (Ωᶜ : Set ℂ), V ζ)ᶜ with hT
  have hTc : IsCompact T := (isCompact_closedBall 0 R).inter_right hWo.isClosed_compl
  have hTΩ : T ⊆ Ω := fun z hz => by
    by_contra hzΩ
    exact hz.2 (hcW hzΩ)
  have hz0T : z0 ∈ T := by
    refine ⟨?_, fun hzW => lt_irrefl c0 (hWh z0 hzW hz0)⟩
    rw [mem_closedBall, dist_zero_right]
    by_contra hgt
    push Not at hgt
    exact lt_irrefl c0 (hR z0 hz0 hgt)
  obtain ⟨z1, hz1T, hmin⟩ := hTc.exists_isMinOn ⟨z0, hz0T⟩ (hcont.mono hTΩ)
  have hz1Ω := hTΩ hz1T
  have hmc0 : h z1 ≤ c0 := hmin hz0T
  have hglob : ∀ z ∈ Ω, h z1 ≤ h z := by
    intro z hz
    by_cases hzT : z ∈ T
    · exact hmin hzT
    · rw [hT, mem_inter_iff, not_and_or, mem_closedBall, dist_zero_right, not_le, notMem_compl_iff] at hzT
      rcases hzT with hzR | hzW
      · exact hmc0.trans (hR z hz hzR).le
      · exact hmc0.trans (hWh z hzW hz).le
  -- the largest disc around `z₁` in `Ω` touches the complement at `ζ`
  have hcl : IsClosed Ωᶜ := hΩ.isClosed_compl
  obtain ⟨ζ, hζ, hdist⟩ := hcl.exists_infDist_eq_dist hne z1
  have hρpos : 0 < infDist z1 Ωᶜ := by
    rw [← infDist_pos_iff_notMem_closure hne, hcl.closure_eq]
    exact fun h => h hz1Ω
  have hζcl : ζ ∈ closure (ball z1 (infDist z1 Ωᶜ)) := by
    rw [closure_ball z1 hρpos.ne', mem_closedBall, dist_comm, hdist]
  obtain ⟨z, hzV, hzball⟩ := mem_closure_iff_nhds.1 hζcl (V ⟨ζ, hζ⟩) ((hVo _).mem_nhds (hVmem _))
  rw [mem_ball] at hzball
  have hzΩ : z ∈ Ω := by
    by_contra hzn
    exact notMem_of_dist_lt_infDist (by rwa [dist_comm] at hzball) hzn
  have hzh : c0 < h z := hVh _ z hzV hzΩ
  rcases (dist_nonneg (x := z) (y := z1)).eq_or_lt with hr0 | hrpos
  · rw [dist_eq_zero.1 hr0.symm] at hzh
    linarith
  · have hball : closedBall z1 (dist z z1) ⊆ Ω := by
      intro w hw
      by_contra hwn
      refine notMem_of_dist_lt_infDist (s := Ωᶜ) (x := z1) ?_ hwn
      rw [mem_closedBall] at hw
      rw [dist_comm]
      exact hw.trans_lt hzball
    have hsph : z ∈ sphere z1 (dist z z1) := by rw [mem_sphere]
    have hlt := lt_circleAverage_of_ge hrpos (hcont.mono (sphere_subset_closedBall.trans hball))
      (fun w hw => hglob w (hball (sphere_subset_closedBall hw))) hsph (by linarith)
    have := hmean z1 (dist z z1) hrpos hball
    linarith

end AuxCommon.Energy
