import Trace86U.CheckSound10

/-!
# Soundness of the 86a upper checker: the left tail and the closed right end

* `leftTailLB_sound`: on `(0, x₀]` (`leftTailPre`: no hat weight left of `x₀`, so `U_{μ₀}(x) ≥ U_{μ₀}(x₀)` there, i.e.
  `U'(x) ≤ U'(x₀)` for `U' = -U_{μ₀}/2`), `leftTailLB / 2^P ≤ F`;
* `leavesOK_sound_Icc`: a nonempty tiling gives `F > 0` on the closed interval.

Fork of the left-tail part of `Trace86.TailSound2`.
-/

open Polynomial Set MeasureTheory

namespace Trace86.UCert

open T86UCore AuxCore AuxCommon

/-- `ℕ`-power with the instance of core Lean (as elaborated in `T86UCore`). -/
local notation:75 a:76 " ^ᶜ " b:75 => @HPow.hPow ℕ ℕ ℕ (@instHPow ℕ ℕ (@instPowNat ℕ instNatPowNat)) a b

theorem cast_powC (a b : ℕ) : ((a ^ᶜ b : ℕ) : ℝ) = (a : ℝ) ^ b := Nat.cast_pow a b

set_option maxRecDepth 20000 in
theorem polys_zero : polys.getD 0 [] = [1, 0] := by decide +kernel

/-! ## A generic fold: the `j = 0` term and the others -/

theorem foldl_ite_add {α : Type*} (p : α → Prop) [DecidablePred p] (f g : α → ℤ) :
    ∀ (l : List α) (a : ℤ), l.foldl (fun acc y => if p y then acc + f y else acc + g y) a =
      a + (l.map (fun y => if p y then f y else g y)).sum
  | [], a => by simp
  | y :: ys, a => by
    rw [List.foldl_cons, foldl_ite_add p f g ys, List.map_cons, List.sum_cons]
    by_cases h : p y
    · simp only [h, ite_true]
      ring
    · simp only [h, ite_false]
      ring

theorem foldl_zipIdx_split {α : Type*} (A B : α → ℤ) (u : ℕ → α) (n : ℕ) (a : ℤ) :
    ((List.range (n + 1)).map (fun j => (u j, j))).foldl
      (fun acc x => if x.2 = 0 then acc + A x.1 else acc + B x.1) a =
      a + A (u 0) + ∑ j ∈ Finset.range n, B (u (j + 1)) := by
  rw [foldl_ite_add (fun x : α × ℕ => x.2 = 0) (fun x => A x.1) (fun x => B x.1), List.map_map,
    list_sum_range, Finset.sum_range_succ']
  simp only [Function.comp_apply, Nat.add_one_ne_zero, ite_false, ite_true]
  ring

/-! ## The left tail -/

/-- The term of `Q₀ = x` in `leftTailLB`. -/
def ltA (X0 D : ℕ) (z : List Int × ℕ × ℕ) : ℤ :=
  fdiv (-(z.2.1 : Int) * (logT TAB L2 X0 D).2) (2 ^ z.2.2)

/-- The term of `Qⱼ`, `j ≥ 1`, in `leftTailLB`. -/
def ltB (X0 D : ℕ) (LD : ℤ × ℤ) (z : List Int × ℕ × ℕ) : ℤ :=
  fdiv (-(z.2.1 : Int) * ((logT TAB L2 (max (encl X0 (taylorR 0 D z.1)).1.natAbs
    (encl X0 (taylorR 0 D z.1)).2.natAbs) 1).2 - ((z.1.length - 1 : Nat) : Int) * LD.1)) (2 ^ z.2.2)

/-- The polynomial part of `leftTailLB`. -/
def polyPartL (X0 D : ℕ) (LD : ℤ × ℤ) : ℤ :=
  (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
    (fun (acc : Int) (x : (List Int × Nat × Nat) × Nat) =>
      if x.2 = 0 then acc + ltA X0 D x.1 else acc + ltB X0 D LD x.1) 0

theorem leftTailLB_eq (X0 k : ℕ) : leftTailLB mkCtx X0 k =
    mkCtx.isLo - mkCtx.m0hi + polyPartL X0 (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) -
      2 * uHi (pointPass TAB L2 mkRecs k X0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) := by
  simp only [leftTailLB, polyPartL, ltA, ltB, ctx_tab, ctx_l2, ctx_rs]

theorem ltA_le {X0 D : ℕ} (hX0 : 0 < X0) (hD : 0 < D) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (X0 : ℝ) / D)
    (desc : List ℤ) (cn cs : ℕ) :
    (ltA X0 D (desc, cn, cs) : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR [1, 0]).eval x|) :=
  leftTail_x_term logT_all hX0 hD hx0 hx cn cs

theorem ltB_le {X0 D : ℕ} (hD : 0 < D) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (X0 : ℝ) / D) (desc : List ℤ) (hQ : (QR desc).eval x ≠ 0) (cn cs : ℕ) :
    (ltB X0 D LD (desc, cn, cs) : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR desc).eval x|) := by
  have h0 : ((0 : ℕ) : ℝ) / D ≤ x := by rw [Nat.cast_zero, zero_div]; exact hx0.le
  have h1 : x ≤ (((0 : ℕ) : ℝ) + X0) / D := by rw [Nat.cast_zero, zero_add]; exact hx
  exact encl_log_term logT_all hLD hD 0 X0 desc h0 h1 hQ cn cs

theorem polyPartL_le {X0 D : ℕ} (hX0 : 0 < X0) (hD : 0 < D) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (X0 : ℝ) / D) (hQx : ∀ j < 21, (QR (polys.getD j [])).eval x ≠ 0) :
    (polyPartL X0 D LD : ℝ) ≤
      2 ^ P * -∑ j ∈ Finset.range 21, cj j * Real.log |(QR (polys.getD j [])).eval x| := by
  unfold polyPartL
  rw [polyList_eq, foldl_zipIdx_split (ltA X0 D) (ltB X0 D LD)
    (fun j => (polys.getD j [], cwNum.getD j 0, cwSh.getD j 0)) 20 0]
  rw [Finset.sum_range_succ' _ 20, zero_add, Int.cast_add, Int.cast_sum]
  have hA := ltA_le hX0 hD hx0 hx (polys.getD 0 []) (cwNum.getD 0 0) (cwSh.getD 0 0)
  have hB : ∀ j ∈ Finset.range 20,
      (ltB X0 D LD (polys.getD (j + 1) [], cwNum.getD (j + 1) 0, cwSh.getD (j + 1) 0) : ℝ) ≤
        2 ^ P * -(cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x|) := by
    intro j hj
    have h := ltB_le hD hLD hx0 hx (polys.getD (j + 1) []) (hQx (j + 1) (by
      have := Finset.mem_range.mp hj
      omega)) (cwNum.getD (j + 1) 0) (cwSh.getD (j + 1) 0)
    refine le_trans h (le_of_eq ?_)
    unfold cj
    ring
  have hsB := Finset.sum_le_sum hB
  rw [polys_zero] at hA ⊢
  have e : 2 ^ P * (-((cwNum.getD 0 0 : ℕ) / 2 ^ (cwSh.getD 0 0) : ℝ) * Real.log |(QR [1, 0]).eval x|) =
      2 ^ P * -(cj 0 * Real.log |(QR [1, 0]).eval x|) := by
    unfold cj
    ring
  rw [e] at hA
  have e2 : 2 ^ P * -(∑ j ∈ Finset.range 20, cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x| +
      cj 0 * Real.log |(QR [1, 0]).eval x|) =
      ∑ j ∈ Finset.range 20, 2 ^ P * -(cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x|) +
        2 ^ P * -(cj 0 * Real.log |(QR [1, 0]).eval x|) := by
    rw [neg_add, mul_add, ← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [e2]
  linarith

/-! ## The potential left of the support -/

/-- `U' = -U_{μ₀}/2` as an integral (closed form). -/
theorem UR_eq_integral (x : ℝ) : UR x = -(∫ y, Real.log (y - x) * pwLin NN eR GR y) / 2 := by
  have h := integral_log_mul_pwLin eR_lt GR_zero GR_NN x
  have h2 : (fun y => Real.log |x - y| * pwLin NN eR GR y) = fun y => Real.log (y - x) * pwLin NN eR GR y := by
    funext y
    rw [Real.log_abs, ← Real.log_neg_eq_log, neg_sub]
  rw [h2] at h
  rw [h]
  unfold UR CR
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- No density at or left of `x₀` if every hat with weight has its left end at or right of `x₀`. -/
theorem pwLin_zero_left {x0 y : ℝ} (hG : ∀ k, 0 < k → k < NN → GR k ≠ 0 → x0 ≤ eR (k - 1)) (hy : y ≤ x0) :
    pwLin NN eR GR y = 0 := by
  unfold pwLin
  apply Finset.sum_eq_zero
  intro k hk
  have hk := Finset.mem_range.mp hk
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hGk : GR k = 0 := by
      by_contra hne
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact hne GR_zero
      · have h3 := hG k hk0 hk hne
        have h4 := eR_lt (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at h4
        linarith
    have hGk1 : GR (k + 1) * (y - eR k) = 0 := by
      by_cases hne : GR (k + 1) = 0
      · rw [hne, zero_mul]
      · have hk1 : k + 1 < NN := by
          rcases Nat.lt_or_ge (k + 1) NN with h5 | h5
          · exact h5
          · exfalso
            apply hne
            rw [show k + 1 = NN by omega]
            exact GR_NN
        have h3 := hG (k + 1) (by omega) hk1 hne
        rw [Nat.add_sub_cancel] at h3
        rw [show y = eR k by linarith, sub_self, mul_zero]
    rw [hGk, zero_mul, zero_add, hGk1, zero_div]
  · rfl

/-- **Left of the support `U_{μ₀}` decreases**: `U'(x) ≤ U'(x₀)` for `0 ≤ x ≤ x₀`. -/
theorem UR_le_UR_x0 {x0 x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ x0)
    (hG : ∀ k, 0 < k → k < NN → GR k ≠ 0 → x0 ≤ eR (k - 1)) : UR x ≤ UR x0 := by
  rw [UR_eq_integral, UR_eq_integral]
  have hmono : ∫ y, Real.log (y - x0) * pwLin NN eR GR y ≤ ∫ y, Real.log (y - x) * pwLin NN eR GR y := by
    refine integral_mono (integrable_mul_pwLin x0 (intervalIntegrable_log_sub x0) eR_lt)
      (integrable_mul_pwLin x (intervalIntegrable_log_sub x) eR_lt) ?_
    intro y
    by_cases hy : y ≤ x0
    · simp only [pwLin_zero_left hG hy, mul_zero, le_refl]
    · push Not at hy
      have hpos : 0 < y - x0 := by linarith
      have hnn : 0 ≤ pwLin NN eR GR y := pwLin_nonneg (fun k _ => GR_nonneg k) y
      apply mul_le_mul_of_nonneg_right _ hnn
      exact Real.log_le_log hpos (by linarith)
  linarith

/-- The hat-weight condition of `leftTailPre`. -/
theorem hat_pre {X0 k : ℕ}
    (h : (List.zip rho nodes).all (fun t => t.1 == 0 || decide (X0 ≤ t.2 * 2 ^ᶜ k)) = true) :
    ∀ j, 0 < j → j < NN → GR j ≠ 0 → (X0 : ℝ) / (DEC * 2 ^ k : ℕ) ≤ eR (j - 1) := by
  intro j hj0 hjN hG
  have hr := rho_length
  have hn := nodes_length
  have hjr : j - 1 < rho.length := by omega
  have hjn : j - 1 < nodes.length := by omega
  have hz : j - 1 < (List.zip rho nodes).length := by simp only [List.length_zip]; omega
  have hall := List.all_eq_true.mp h _ (List.getElem_mem hz)
  rw [List.getElem_zip] at hall
  have hrho : rho.getD (j - 1) 0 = rho[j - 1]'hjr := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some]
  have hnod : nodes.getD (j - 1) 0 = nodes[j - 1]'hjn := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjn, Option.getD_some]
  generalize rho[j - 1]'hjr = r at hall hrho
  generalize nodes[j - 1]'hjn = n at hall hnod
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  rcases hall with h0 | hle
  · exfalso
    apply hG
    unfold GR rhoR
    rw [if_pos ⟨hj0, hjN⟩, hrho, h0]
    simp
  · unfold eR
    rw [hnod]
    have h1 : ((X0 : ℕ) : ℝ) ≤ ((n * 2 ^ᶜ k : ℕ) : ℝ) := Nat.cast_le.mpr hle
    rw [Nat.cast_mul, cast_powC, Nat.cast_ofNat] at h1
    have hDv : ((DEC * 2 ^ k : ℕ) : ℝ) = 10 ^ 12 * 2 ^ k := by push_cast; rw [DEC_real]
    rw [hDv, div_le_div_iff₀ (by positivity) (by norm_num)]
    calc (X0 : ℝ) * 10 ^ 12 ≤ ((n : ℝ) * 2 ^ k) * 10 ^ 12 := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = (n : ℝ) * (10 ^ 12 * 2 ^ k) := by ring

/-- **The left tail** `(0, x₀]`. -/
theorem leftTailLB_sound {X0 k : ℕ} (hpre : leftTailPre X0 k = true)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (X0 : ℝ) / (DEC * 2 ^ k : ℕ))
    (hQx : ∀ j < 21, (QR (polys.getD j [])).eval x ≠ 0) :
    (leftTailLB mkCtx X0 k : ℝ) / 2 ^ P ≤ FR x := by
  have hpre' := hpre
  simp only [leftTailPre, Bool.and_eq_true, decide_eq_true_eq] at hpre'
  obtain ⟨⟨hX0, -⟩, hall⟩ := hpre'
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  rw [leftTailLB_eq]
  have hLDs := logT_D k
  have hU0 : 2 ^ P * UR ((X0 : ℝ) / (DEC * 2 ^ k : ℕ)) ≤
      (uHi (pointPass TAB L2 mkRecs k X0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) : ℝ) :=
    uHi_le_of hD (pointPass_sound (X := X0) hLDs).2
  have hpp := polyPartL_le hX0 hD hLDs hx0 hx hQx
  have hUx : UR x ≤ UR ((X0 : ℝ) / (DEC * 2 ^ k : ℕ)) := UR_le_UR_x0 hx0.le hx (hat_pre hall)
  generalize uHi (pointPass TAB L2 mkRecs k X0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) = uh at hU0 ⊢
  generalize polyPartL X0 (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) = pp at hpp ⊢
  have h2 := isLo_le
  have h3 := m0hi_eq
  have hFR : FR x = c0R - ∑ j ∈ Finset.range 21, cj j * Real.log |(QR (polys.getD j [])).eval x| - 2 * UR x := by
    unfold FR; rw [FR_poly_sum]
  rw [hFR, div_le_iff₀ hP]
  push_cast
  have hUxP := mul_le_mul_of_nonneg_left hUx hP.le
  linarith

/-! ## The closed right end -/

/-- **A nonempty tiling, closed interval.** -/
theorem leavesOK_sound_Icc : ∀ (ls : List Leaf) (X kx XT kT : ℕ), ls ≠ [] →
    leavesOK mkCtx X kx ls XT kT = true →
    ∀ x ∈ Icc ((X : ℝ) / (DEC * 2 ^ kx : ℕ)) ((XT : ℝ) / (DEC * 2 ^ kT : ℕ)),
      (∀ j < 21, (QR (polys.getD j [])).eval x ≠ 0) → 0 < FR x
  | [], _, _, _, _, h, _ => absurd rfl h
  | [l], X, kx, XT, kT, _, h => by
    simp only [leavesOK, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨-, hleaf⟩ := leafOK_sound h2
    have he1 := ptEq_real h1
    have he2 := ptEq_real h3
    intro x hx hQ
    rw [he1, ← he2] at hx
    exact hleaf x hx hQ
  | l :: l' :: ls, X, kx, XT, kT, _, h => by
    have h' : (ptEq X kx l.X1 l.k && leafOK mkCtx l && leavesOK mkCtx l.X2 l.k (l' :: ls) XT kT) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    have hrest := leavesOK_sound_Icc (l' :: ls) l.X2 l.k XT kT (List.cons_ne_nil _ _) h3
    obtain ⟨hlt, hleaf⟩ := leafOK_sound h2
    have he := ptEq_real h1
    intro x hx hQ
    rw [he] at hx
    by_cases hxl : x ≤ (l.X2 : ℝ) / (DEC * 2 ^ l.k : ℕ)
    · exact hleaf x ⟨hx.1, hxl⟩ hQ
    · exact hrest x ⟨le_of_lt (not_le.mp hxl), hx.2⟩ hQ

end Trace86.UCert
