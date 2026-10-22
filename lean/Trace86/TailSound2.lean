import Trace86.CheckSound9

/-!
# Soundness of the 86a checker: the two tails (adapted from the companion Mahler-measure formalization)

* `leftTailLB_sound`: on `(0, x₀]` (`leftTailPre`: no hat weight left of `x₀`, so `U(x) ≤ U(0)` there),
  `leftTailLB / 2^P ≤ F`;
* `rightTailLB_sound`: on `[x_t, ∞)` (`rightTailPre`: `x_t ≥ max(1, e_N, κ')`, `κ' = ∑ cⱼ deg Qⱼ + 2 s`; then
  `x - κ' log x` increases on `[x_t, ∞)`), `rightTailLB / 2^P ≤ F`.

Computed records and the large closed constants (`sNum`, the context fields) are kept opaque by `generalize` before
any tactic that could reduce them.
-/

open Polynomial Set MeasureTheory

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

/-- `ℕ`-power with the instance of core Lean (as elaborated in `T86Core`), so that the restated checker terms below
are syntactically those of `T86Core` (no defeq check that could evaluate the certificate data). -/
local notation:75 a:76 " ^ᶜ " b:75 => @HPow.hPow ℕ ℕ ℕ (@instHPow ℕ ℕ (@instPowNat ℕ instNatPowNat)) a b

theorem cast_powC (a b : ℕ) : ((a ^ᶜ b : ℕ) : ℝ) = (a : ℝ) ^ b := Nat.cast_pow a b

/-! ## Constants -/

set_option maxRecDepth 20000 in
theorem cwSh_max : cwSh.foldl max 0 = 48 := by decide +kernel

set_option maxRecDepth 20000 in
theorem cwSh_le : ∀ j < 15, cwSh.getD j 0 ≤ 48 := by decide +kernel

set_option maxRecDepth 20000 in
theorem polys_zero : polys.getD 0 [] = [1, 0] := by decide +kernel

/-- `κ' · 2^S sDen` (`kNum` of `rightTailLB`, `κ' = ∑ cⱼ deg Qⱼ + 2 s`). -/
def lhsV : ℕ :=
  (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ᶜ (cwSh.foldl max 0 - x.2.2) * sDen) 0 +
    2 * sNum * 2 ^ᶜ (cwSh.foldl max 0)

/-- The common denominator `2^S sDen`. -/
def kDenV : ℕ := 2 ^ᶜ (cwSh.foldl max 0) * sDen

theorem kDenV_pos : (0 : ℝ) < (kDenV : ℝ) := by
  have h : 0 < kDenV := Nat.mul_pos (Nat.two_pow_pos _) sDen_pos
  exact_mod_cast h

/-- The budget sum with the large constants as parameters (keeps the kernel away from `sDen`, `sNum`). -/
theorem lhs_gen (S sD sN : ℕ) :
    (List.zip polys (List.zip cwNum cwSh)).foldl
      (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ᶜ (S - x.2.2) * sD) 0 + 2 * sN * 2 ^ᶜ S =
    ∑ j ∈ Finset.range 15, cwNum.getD j 0 * ((polys.getD j []).length - 1) * 2 ^ᶜ (S - cwSh.getD j 0) * sD +
      2 * sN * 2 ^ᶜ S := by
  have hsum : ∀ (g : ℕ → ℕ), ((List.range 15).map g).sum = ∑ j ∈ Finset.range 15, g j :=
    fun g => list_sum_range g 15
  rw [polyZip_eq, foldl_add_eq_sum, zero_add, List.map_map, hsum]
  rfl

theorem lhsV_eq : lhsV =
    ∑ j ∈ Finset.range 15, cwNum.getD j 0 * ((polys.getD j []).length - 1) *
      2 ^ᶜ (cwSh.foldl max 0 - cwSh.getD j 0) * sDen + 2 * sNum * 2 ^ᶜ (cwSh.foldl max 0) :=
  lhs_gen _ _ _

/-- `lhs / (2^S sDen) = ∑ cⱼ dⱼ + 2 s`. -/
theorem lhsV_div : (lhsV : ℝ) / (kDenV : ℝ) =
    ∑ j ∈ Finset.range 15, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) + 2 * sR := by
  have hD : (0 : ℝ) < (sDen : ℝ) := by exact_mod_cast sDen_pos
  have hle : ∀ j < 15, cwSh.getD j 0 ≤ cwSh.foldl max 0 := by
    rw [cwSh_max]
    exact cwSh_le
  rw [lhsV_eq, kDenV, sR_eq]
  generalize cwSh.foldl max 0 = S at hle ⊢
  generalize sNum = sN
  generalize sDen = sD at hD ⊢
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  push_cast [cast_powC]
  rw [div_eq_iff (mul_pos hS hD).ne', add_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [pow_sub₀ (2 : ℝ) two_ne_zero (hle j (Finset.mem_range.mp hj))]
    unfold cj
    field_simp
  · field_simp

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

theorem leftTailLB_eq (X0 k : ℕ) : leftTailLB (mkCtx iLoNum 128) X0 k =
    (mkCtx iLoNum 128).isLo - (mkCtx iLoNum 128).m0hi +
      polyPartL X0 (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) -
      2 * uHi (pointPass TAB L2 mkRecs k 0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) := by
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
    (hx : x ≤ (X0 : ℝ) / D) (hQx : ∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) :
    (polyPartL X0 D LD : ℝ) ≤
      2 ^ P * -∑ j ∈ Finset.range 15, cj j * Real.log |(QR (polys.getD j [])).eval x| := by
  unfold polyPartL
  rw [polyList_eq, foldl_zipIdx_split (ltA X0 D) (ltB X0 D LD)
    (fun j => (polys.getD j [], cwNum.getD j 0, cwSh.getD j 0)) 14 0]
  rw [Finset.sum_range_succ' _ 14, zero_add, Int.cast_add, Int.cast_sum]
  have hA := ltA_le hX0 hD hx0 hx (polys.getD 0 []) (cwNum.getD 0 0) (cwSh.getD 0 0)
  have hB : ∀ j ∈ Finset.range 14,
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
  have e2 : 2 ^ P * -(∑ j ∈ Finset.range 14, cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x| +
      cj 0 * Real.log |(QR [1, 0]).eval x|) =
      ∑ j ∈ Finset.range 14, 2 ^ P * -(cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x|) +
        2 ^ P * -(cj 0 * Real.log |(QR [1, 0]).eval x|) := by
    rw [neg_add, mul_add, ← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [e2]
  linarith

/-! ## The potential left of the support -/

theorem UR_eq_integral (x : ℝ) : UR x = ∫ y, Real.log (y - x) * pwLin NN eR GR y := by
  have h := integral_log_mul_pwLin eR_lt GR_zero GR_NN x
  have h2 : (fun y => Real.log |x - y| * pwLin NN eR GR y) = fun y => Real.log (y - x) * pwLin NN eR GR y := by
    funext y
    rw [Real.log_abs, ← Real.log_neg_eq_log, neg_sub]
  rw [h2] at h
  unfold UR CR
  exact h.symm

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

/-- **Left of the support the potential decreases**: `U(x) ≤ U(0)` for `0 ≤ x ≤ x₀`. -/
theorem UR_le_UR_zero {x0 x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ x0)
    (hG : ∀ k, 0 < k → k < NN → GR k ≠ 0 → x0 ≤ eR (k - 1)) : UR x ≤ UR 0 := by
  rw [UR_eq_integral, UR_eq_integral]
  refine integral_mono (integrable_mul_pwLin x (intervalIntegrable_log_sub x) eR_lt)
    (integrable_mul_pwLin 0 (intervalIntegrable_log_sub 0) eR_lt) ?_
  intro y
  by_cases hy : y ≤ x0
  · simp only [pwLin_zero_left hG hy, mul_zero, le_refl]
  · push Not at hy
    have hpos : 0 < y - x := by linarith
    have hnn : 0 ≤ pwLin NN eR GR y := pwLin_nonneg (fun k _ => GR_nonneg k) y
    apply mul_le_mul_of_nonneg_right _ hnn
    rw [sub_zero]
    exact Real.log_le_log hpos (by linarith)

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
theorem leftTailLB_sound (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) {X0 k : ℕ} (hpre : leftTailPre X0 k = true)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (X0 : ℝ) / (DEC * 2 ^ k : ℕ))
    (hQx : ∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) :
    (leftTailLB (mkCtx iLoNum 128) X0 k : ℝ) / 2 ^ P ≤ FR x := by
  have hpre' := hpre
  simp only [leftTailPre, Bool.and_eq_true, decide_eq_true_eq] at hpre'
  obtain ⟨⟨hX0, -⟩, hall⟩ := hpre'
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  rw [leftTailLB_eq]
  have hLDs := logT_D k
  have hU0 : 2 ^ P * UR (((0 : ℕ) : ℝ) / (DEC * 2 ^ k : ℕ)) ≤
      (uHi (pointPass TAB L2 mkRecs k 0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) : ℝ) :=
    uHi_le_of hD (pointPass_sound (X := 0) hLDs).2
  rw [Nat.cast_zero, zero_div] at hU0
  have hpp := polyPartL_le hX0 hD hLDs hx0 hx hQx
  have hUx : UR x ≤ UR 0 := UR_le_UR_zero hx0.le hx (hat_pre hall)
  generalize uHi (pointPass TAB L2 mkRecs k 0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) = uh at hU0 ⊢
  generalize polyPartL X0 (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) = pp at hpp ⊢
  have h2 := isLo_le hI
  have h3 := m0hi_ge
  have hFR : FR x = x - lamR - ∑ j ∈ Finset.range 15, cj j * Real.log |(QR (polys.getD j [])).eval x| -
      2 * UR x + IR / sR := by
    unfold FR; rw [FR_poly_sum]
  rw [hFR, div_le_iff₀ hP]
  push_cast
  have hUxP := mul_le_mul_of_nonneg_left hUx hP.le
  have hxP : 0 ≤ 2 ^ P * x := mul_nonneg hP.le hx0.le
  linarith

/-! ## The right tail -/

/-- `klog` of `rightTailLB`: an upper bound of `2^P κ' log x_t`. -/
def klogV (Xt : ℕ) : ℤ := cdiv ((lhsV : ℤ) * (logT TAB L2 Xt DEC).2) kDenV

/-- The term of one polynomial in `rightTailLB`. -/
def rtA (Xt : ℕ) (z : List Int × ℕ × ℕ) : ℤ :=
  fdiv (-(z.2.1 : Int) * (logT TAB L2
    (z.1.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ᶜ q.2 * Xt ^ᶜ (z.1.length - 1 - q.2)) 0)
    (Xt ^ᶜ (z.1.length - 1))).2) (2 ^ᶜ z.2.2)

/-- The polynomial part of `rightTailLB`. -/
def aPartR (Xt : ℕ) : ℤ :=
  (List.zip polys (List.zip cwNum cwSh)).foldl (fun (acc : Int) (x : List Int × Nat × Nat) => acc + rtA Xt x) 0

theorem rightTailLB_eq (Xt : ℕ) : rightTailLB (mkCtx iLoNum 128) Xt =
    mainLo Xt DEC - klogV Xt - (mkCtx iLoNum 128).m0hi + (mkCtx iLoNum 128).isLo + aPartR Xt := by
  simp only [rightTailLB, klogV, kDenV, lhsV, aPartR, rtA, ctx_tab, ctx_l2]

theorem foldl_map_range_add {α : Type*} (h : ℕ → α) (g : α → ℤ) (n : ℕ) :
    ((List.range n).map h).foldl (fun acc y => acc + g y) 0 = ∑ j ∈ Finset.range n, g (h j) := by
  rw [foldl_add_eq_sum, zero_add, List.map_map, list_sum_range]
  rfl

theorem rtA_le {Xt : ℕ} (hXt : 0 < Xt) {x : ℝ} (hx : (Xt : ℝ) / DEC ≤ x) (desc : List ℤ)
    (hQ : (QR desc).eval x ≠ 0) (cn cs : ℕ) :
    (rtA Xt (desc, cn, cs) : ℝ) ≤
      2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (Real.log |(QR desc).eval x| - (desc.length - 1 : ℕ) * Real.log x)) :=
  rightTail_poly_term logT_all desc hXt hx hQ cn cs

theorem aPartR_le {Xt : ℕ} (hXt : 0 < Xt) {x : ℝ} (hx : (Xt : ℝ) / DEC ≤ x)
    (hQx : ∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) :
    (aPartR Xt : ℝ) ≤ 2 ^ P * ∑ j ∈ Finset.range 15, -(cj j * (Real.log |(QR (polys.getD j [])).eval x| -
      (((polys.getD j []).length - 1 : ℕ) : ℝ) * Real.log x)) := by
  unfold aPartR
  rw [polyZip_eq, foldl_map_range_add, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := rtA_le hXt hx (polys.getD j []) (hQx j (Finset.mem_range.mp hj)) (cwNum.getD j 0) (cwSh.getD j 0)
  refine le_trans h (le_of_eq ?_)
  unfold cj
  ring

theorem klogV_ge {Xt : ℕ} (hXt : 0 < Xt) :
    2 ^ P * ((lhsV : ℝ) / kDenV * Real.log ((Xt : ℝ) / DEC)) ≤ (klogV Xt : ℝ) := by
  have hl := logT_all Xt DEC hXt (by decide)
  have hK := kDenV_pos
  unfold klogV
  generalize lhsV = L
  generalize kDenV = kD at hK ⊢
  generalize logT TAB L2 Xt DEC = lx at hl ⊢
  have hKn : 0 < kD := by exact_mod_cast hK
  refine le_trans ?_ (le_cdiv ((L : ℤ) * lx.2) hKn)
  rw [le_div_iff₀ hK]
  have e : 2 ^ P * ((L : ℝ) / kD * Real.log ((Xt : ℝ) / DEC)) * kD =
      (L : ℝ) * (2 ^ P * Real.log ((Xt : ℝ) / DEC)) := by
    field_simp
  rw [e]
  push_cast
  exact mul_le_mul_of_nonneg_left hl.2 (Nat.cast_nonneg _)

set_option maxRecDepth 200000 in
theorem nodes_getLast : nodes.getLast?.getD 0 = nodes.getD NN 0 := by decide +kernel

theorem rightTailPre_iff (Xt : ℕ) :
    rightTailPre Xt = true ↔ (DEC ≤ Xt ∧ nodes.getLast?.getD 0 ≤ Xt) ∧ lhsV * DEC ≤ Xt * kDenV := by
  simp only [rightTailPre, lhsV, kDenV, Bool.and_eq_true, decide_eq_true_eq]

/-- **The right tail** `[x_t, ∞)`. -/
theorem rightTailLB_sound (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) {Xt : ℕ} (hpre : rightTailPre Xt = true) {x : ℝ}
    (hx : (Xt : ℝ) / DEC ≤ x) (hQx : ∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) :
    (rightTailLB (mkCtx iLoNum 128) Xt : ℝ) / 2 ^ P ≤ FR x := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := (rightTailPre_iff Xt).mp hpre
  rw [nodes_getLast] at h2
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hDEC : (0 : ℝ) < DEC := by rw [DEC_real]; norm_num
  have hXt : 0 < Xt := lt_of_lt_of_le (by decide) h1
  have hxt1 : (1 : ℝ) ≤ (Xt : ℝ) / DEC := by
    rw [le_div_iff₀ hDEC, one_mul]
    exact_mod_cast h1
  have heN : eR NN ≤ (Xt : ℝ) / DEC := by
    unfold eR
    rw [← DEC_real]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h2) hDEC.le
  have hK := kDenV_pos
  have hκxt : (lhsV : ℝ) / kDenV ≤ (Xt : ℝ) / DEC := by
    rw [div_le_div_iff₀ hK hDEC]
    exact_mod_cast h3
  have hκ0 : 0 ≤ (lhsV : ℝ) / kDenV := div_nonneg (Nat.cast_nonneg _) hK.le
  rw [rightTailLB_eq]
  have hm := mainLo_le Xt DEC (by decide)
  have hk := klogV_ge hXt
  have ha := aPartR_le hXt hx hQx
  have hU : UR x ≤ sR * Real.log x := UR_le_sR_log (le_trans heN hx)
  have h2' := isLo_le hI
  have h3' := m0hi_ge
  have hkap := lhsV_div
  have hsplit : ∑ j ∈ Finset.range 15, -(cj j * (Real.log |(QR (polys.getD j [])).eval x| -
      (((polys.getD j []).length - 1 : ℕ) : ℝ) * Real.log x)) =
      -(∑ j ∈ Finset.range 15, cj j * Real.log |(QR (polys.getD j [])).eval x|) +
        (∑ j ∈ Finset.range 15, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ)) * Real.log x := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsplit] at ha
  have hFR : FR x = x - lamR - ∑ j ∈ Finset.range 15, cj j * Real.log |(QR (polys.getD j [])).eval x| -
      2 * UR x + IR / sR := by
    unfold FR
    rw [FR_poly_sum]
  rw [hFR]
  generalize klogV Xt = kl at hk ⊢
  generalize aPartR Xt = ap at ha ⊢
  generalize (lhsV : ℝ) / kDenV = κ at hk hκxt hκ0 hkap
  generalize (Xt : ℝ) / DEC = xt at hk hκxt hxt1 heN hx hm
  generalize ∑ j ∈ Finset.range 15, cj j * Real.log |(QR (polys.getD j [])).eval x| = A at ha ⊢
  generalize ∑ j ∈ Finset.range 15, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) = Dd at ha hkap
  have hx1 : (1 : ℝ) ≤ x := le_trans hxt1 hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxt0 : 0 < xt := lt_of_lt_of_le one_pos hxt1
  -- `x - κ log x` increases on `[x_t, ∞)` (`κ ≤ x_t`)
  have hmono : xt - κ * Real.log xt ≤ x - κ * Real.log x := by
    have hlog : Real.log x - Real.log xt ≤ (x - xt) / xt := by
      rw [← Real.log_div hx0.ne' hxt0.ne']
      calc Real.log (x / xt) ≤ x / xt - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hxt0)
        _ = (x - xt) / xt := by field_simp
    have h4 : κ * (Real.log x - Real.log xt) ≤ κ * ((x - xt) / xt) := mul_le_mul_of_nonneg_left hlog hκ0
    have h5 : κ * ((x - xt) / xt) ≤ x - xt := by
      rw [mul_div_assoc', div_le_iff₀ hxt0]
      have h6 : 0 ≤ x - xt := by linarith
      have h7 := mul_le_mul_of_nonneg_left hκxt h6
      linarith
    linarith
  rw [div_le_iff₀ hP]
  push_cast
  have hmonoP := mul_le_mul_of_nonneg_left hmono hP.le
  have hUP := mul_le_mul_of_nonneg_left hU hP.le
  rw [hkap] at hmonoP hk
  have e1 : 2 ^ P * (x - (Dd + 2 * sR) * Real.log x) =
      2 ^ P * x - 2 ^ P * (Dd * Real.log x) - 2 * (2 ^ P * (sR * Real.log x)) := by ring
  have e2 : 2 ^ P * (-A + Dd * Real.log x) = -(2 ^ P * A) + 2 ^ P * (Dd * Real.log x) := by ring
  have e3 : (x - lamR - A - 2 * UR x + IR / sR) * 2 ^ P =
      2 ^ P * x - 2 ^ P * lamR - 2 ^ P * A - 2 * (2 ^ P * UR x) + 2 ^ P * (IR / sR) := by ring
  have e4 : 2 ^ P * (xt - (Dd + 2 * sR) * Real.log xt) =
      2 ^ P * xt - 2 ^ P * ((Dd + 2 * sR) * Real.log xt) := by ring
  rw [e1, e4] at hmonoP
  rw [e2] at ha
  rw [e3]
  linarith

end Trace86.Cert
