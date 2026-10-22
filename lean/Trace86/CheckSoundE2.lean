import Trace86.CheckSound7

/-!
# Soundness of the end-point form, part 2: a second-order bound for sums of logarithms

For nodes `e_i` outside `[p, q]` and `κ_i ≥ 0` with `κ_i dist(e_i, [p, q])² ≥ -2 C_i`, on `[p, q]`:
`∑ -2 C_i log |y - e_i| ≤ max(the value at p, the value at q) + (∑ κ_i) (q - p)² / 8`, because every
`-2 C_i log |z - e_i| + κ_i (z - p)(z - q) / 2` is convex there (its derivative is monotone).
-/

open Set

namespace Trace86.Cert

/-- Distance of a point `e` outside `[p, q]` to `[p, q]`. -/
noncomputable def distPQ (p q e : ℝ) : ℝ := if e < p then p - e else e - q

theorem convexOn_logterm_left {p q e c κ : ℝ} (hpq : p < q) (he : e < p) (hκ : 0 ≤ κ)
    (hκc : -2 * c ≤ κ * (p - e) ^ 2) :
    ConvexOn ℝ (Icc p q) (fun z => -2 * c * Real.log (z - e) + κ * ((z - p) * (z - q)) / 2) := by
  have hderiv : ∀ z ∈ Ioo p q, HasDerivAt (fun z => -2 * c * Real.log (z - e) + κ * ((z - p) * (z - q)) / 2)
      (-2 * c * (z - e)⁻¹ + κ * (2 * z - p - q) / 2) z := by
    intro z hz
    have hz0 : z - e ≠ 0 := by have := hz.1; intro h; linarith
    have h1 : HasDerivAt (fun z => z - e) 1 z := (hasDerivAt_id z).sub_const e
    have h2 := h1.log hz0
    have h3 : HasDerivAt (fun z => (z - p) * (z - q)) (1 * (z - q) + (z - p) * 1) z :=
      ((hasDerivAt_id z).sub_const p).mul ((hasDerivAt_id z).sub_const q)
    have := (h2.const_mul (-2 * c)).add ((h3.const_mul κ).div_const 2)
    convert this using 1
    field_simp
    ring
  apply MonotoneOn.convexOn_of_deriv (convex_Icc p q)
  · apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro z hz
      have := hz.1
      intro h
      simp only [Pi.sub_apply, id_eq] at h
      linarith
    · fun_prop
  · rw [interior_Icc]
    intro z hz
    exact (hderiv z hz).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro z1 hz1 z2 hz2 hle
    rw [(hderiv z1 hz1).deriv, (hderiv z2 hz2).deriv]
    have ha : 0 < z1 - e := by linarith [hz1.1]
    have hb : 0 < z2 - e := by linarith [hz2.1]
    have hd : (p - e) ^ 2 ≤ (z1 - e) * (z2 - e) := by nlinarith [hz1.1, hz2.1]
    have key : 0 ≤ (z2 - z1) * (2 * c + κ * ((z1 - e) * (z2 - e))) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hd hκ]
    have e1 : (-2 * c * (z2 - e)⁻¹ + κ * (2 * z2 - p - q) / 2) - (-2 * c * (z1 - e)⁻¹ + κ * (2 * z1 - p - q) / 2) =
        (z2 - z1) * (2 * c + κ * ((z1 - e) * (z2 - e))) / ((z1 - e) * (z2 - e)) := by
      field_simp
      ring
    have : 0 ≤ (z2 - z1) * (2 * c + κ * ((z1 - e) * (z2 - e))) / ((z1 - e) * (z2 - e)) :=
      div_nonneg key (by positivity)
    linarith

theorem convexOn_logterm_right {p q e c κ : ℝ} (hpq : p < q) (he : q < e) (hκ : 0 ≤ κ)
    (hκc : -2 * c ≤ κ * (e - q) ^ 2) :
    ConvexOn ℝ (Icc p q) (fun z => -2 * c * Real.log (e - z) + κ * ((z - p) * (z - q)) / 2) := by
  have hderiv : ∀ z ∈ Ioo p q, HasDerivAt (fun z => -2 * c * Real.log (e - z) + κ * ((z - p) * (z - q)) / 2)
      (2 * c * (e - z)⁻¹ + κ * (2 * z - p - q) / 2) z := by
    intro z hz
    have hz0 : e - z ≠ 0 := by have := hz.2; intro h; linarith
    have h1 : HasDerivAt (fun z => e - z) (0 - 1) z := (hasDerivAt_const z e).sub (hasDerivAt_id z)
    have h2 := h1.log hz0
    have h3 : HasDerivAt (fun z => (z - p) * (z - q)) (1 * (z - q) + (z - p) * 1) z :=
      ((hasDerivAt_id z).sub_const p).mul ((hasDerivAt_id z).sub_const q)
    have := (h2.const_mul (-2 * c)).add ((h3.const_mul κ).div_const 2)
    convert this using 1
    field_simp
    ring
  apply MonotoneOn.convexOn_of_deriv (convex_Icc p q)
  · apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (continuousOn_const.sub continuousOn_id)
      intro z hz
      have := hz.2
      intro h
      simp only [Pi.sub_apply, id_eq] at h
      linarith
    · fun_prop
  · rw [interior_Icc]
    intro z hz
    exact (hderiv z hz).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro z1 hz1 z2 hz2 hle
    rw [(hderiv z1 hz1).deriv, (hderiv z2 hz2).deriv]
    have ha : 0 < e - z1 := by linarith [hz1.2]
    have hb : 0 < e - z2 := by linarith [hz2.2]
    have hd : (e - q) ^ 2 ≤ (e - z1) * (e - z2) := by nlinarith [hz1.2, hz2.2]
    have key : 0 ≤ (z2 - z1) * (2 * c + κ * ((e - z1) * (e - z2))) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hd hκ]
    have e1 : (2 * c * (e - z2)⁻¹ + κ * (2 * z2 - p - q) / 2) - (2 * c * (e - z1)⁻¹ + κ * (2 * z1 - p - q) / 2) =
        (z2 - z1) * (2 * c + κ * ((e - z1) * (e - z2))) / ((e - z1) * (e - z2)) := by
      field_simp
      ring
    have : 0 ≤ (z2 - z1) * (2 * c + κ * ((e - z1) * (e - z2))) / ((e - z1) * (e - z2)) :=
      div_nonneg key (by positivity)
    linarith

theorem convexOn_logterm {p q e c κ : ℝ} (hpq : p < q) (he : e < p ∨ q < e) (hκ : 0 ≤ κ)
    (hκc : -2 * c ≤ κ * distPQ p q e ^ 2) :
    ConvexOn ℝ (Icc p q) (fun z => -2 * c * Real.log |z - e| + κ * ((z - p) * (z - q)) / 2) := by
  rcases he with he | he
  · have hd : distPQ p q e = p - e := by simp [distPQ, he]
    rw [hd] at hκc
    apply (convexOn_logterm_left hpq he hκ hκc).congr
    intro z hz
    simp only
    rw [abs_of_pos (by linarith [hz.1] : 0 < z - e)]
  · have hd : distPQ p q e = e - q := by simp [distPQ, not_lt.mpr (by linarith : p ≤ e)]
    rw [hd] at hκc
    apply (convexOn_logterm_right hpq he hκ hκc).congr
    intro z hz
    simp only
    rw [abs_sub_comm, abs_of_pos (by linarith [hz.2] : 0 < e - z)]

/-- **The second-order bound.** -/
theorem second_order_le {p q : ℝ} (hpq : p < q) (s : Finset ℕ) (C e κ : ℕ → ℝ)
    (he : ∀ i ∈ s, e i < p ∨ q < e i) (hκ : ∀ i ∈ s, 0 ≤ κ i)
    (hκc : ∀ i ∈ s, -2 * C i ≤ κ i * distPQ p q (e i) ^ 2) {y : ℝ} (hy : y ∈ Icc p q) :
    ∑ i ∈ s, -2 * C i * Real.log |y - e i| ≤
      max (∑ i ∈ s, -2 * C i * Real.log |p - e i|) (∑ i ∈ s, -2 * C i * Real.log |q - e i|) +
        (∑ i ∈ s, κ i) * (q - p) ^ 2 / 8 := by
  set ψ : ℝ → ℝ := fun z => ∑ i ∈ s, (-2 * C i * Real.log |z - e i| + κ i * ((z - p) * (z - q)) / 2) with hψ
  have hconv : ConvexOn ℝ (Icc p q) ψ :=
    convexOn_finset_sum (convex_Icc p q) s _ (fun i hi => convexOn_logterm hpq (he i hi) (hκ i hi) (hκc i hi))
  have hpI : p ∈ Icc p q := ⟨le_rfl, hpq.le⟩
  have hqI : q ∈ Icc p q := ⟨hpq.le, le_rfl⟩
  have hseg : y ∈ segment ℝ p q := by rw [segment_eq_Icc hpq.le]; exact hy
  have h := hconv.le_on_segment hpI hqI hseg
  have hψz : ∀ z, ψ z = ∑ i ∈ s, -2 * C i * Real.log |z - e i| + (∑ i ∈ s, κ i) * ((z - p) * (z - q)) / 2 := by
    intro z
    simp only [hψ]
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_div]
  rw [hψz, hψz, hψz] at h
  simp only [sub_self, mul_zero, zero_mul, zero_div, add_zero] at h
  have hK : 0 ≤ ∑ i ∈ s, κ i := Finset.sum_nonneg hκ
  have hq : (y - p) * (q - y) ≤ (q - p) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * y - p - q)]
  have h2 : (∑ i ∈ s, κ i) * ((y - p) * (q - y)) ≤ (∑ i ∈ s, κ i) * ((q - p) ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hq hK
  have e2 : (∑ i ∈ s, κ i) * ((y - p) * (y - q)) / 2 = -((∑ i ∈ s, κ i) * ((y - p) * (q - y)) / 2) := by ring
  rw [e2] at h
  linarith

end Trace86.Cert
