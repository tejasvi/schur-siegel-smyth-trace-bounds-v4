import Trace86U.CheckSound9

/-!
# The 86a upper certificate polynomials (fork of `Trace86.CertData`)

Degrees, nonvanishing and monicity of the `Qc j = Qd (polys j)` (leading coefficient `1`, checked on the data), and the
bridge `‖Qⱼ(x)‖ = |Qⱼ(x)|` for real `x`.
-/

open Polynomial

namespace Trace86.UCert

open T86UCore AuxCore AuxCommon

/-! ## Horner polynomials: degree and nonvanishing -/

theorem foldl_horner_shift (t : List ℤ) (p : ℤ[X]) :
    t.foldl (fun acc a => acc * X + Polynomial.C a) p =
      p * X ^ t.length + t.foldl (fun acc a => acc * X + Polynomial.C a) 0 := by
  induction t generalizing p with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (p * X + Polynomial.C b), ih (0 * X + Polynomial.C b)]
    ring

theorem Qd_cons (b : ℤ) (t : List ℤ) : Qd (b :: t) = Polynomial.C b * X ^ t.length + Qd t := by
  unfold Qd
  rw [List.foldl_cons, foldl_horner_shift]
  ring

theorem degree_Qd_lt (t : List ℤ) : (Qd t).degree < t.length := by
  induction t with
  | nil => simp [Qd]
  | cons b t ih =>
    rw [Qd_cons, List.length_cons]
    calc (Polynomial.C b * X ^ t.length + Qd t).degree
        ≤ max (Polynomial.C b * X ^ t.length).degree (Qd t).degree := degree_add_le _ _
      _ < ((t.length + 1 : ℕ) : WithBot ℕ) := by
        apply max_lt
        · exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast Nat.lt_succ_self _)
        · exact lt_trans ih (by exact_mod_cast Nat.lt_succ_self _)

theorem degree_Qd_lt_lead {b : ℤ} (hb : b ≠ 0) (t : List ℤ) :
    (Qd t).degree < (Polynomial.C b * X ^ t.length).degree := by
  rw [degree_C_mul_X_pow t.length hb]
  exact degree_Qd_lt t

theorem natDegree_Qd_cons {b : ℤ} (hb : b ≠ 0) (t : List ℤ) : (Qd (b :: t)).natDegree = t.length := by
  rw [Qd_cons, natDegree_add_eq_left_of_degree_lt (degree_Qd_lt_lead hb t),
    natDegree_C_mul_X_pow t.length b hb]

theorem Qd_cons_ne_zero {b : ℤ} (hb : b ≠ 0) (t : List ℤ) : Qd (b :: t) ≠ 0 := by
  intro h
  have hdeg := congrArg degree h
  rw [Qd_cons, degree_add_eq_left_of_degree_lt (degree_Qd_lt_lead hb t), degree_C_mul_X_pow t.length hb,
    degree_zero] at hdeg
  exact WithBot.coe_ne_bot hdeg

/-! ## The certificate polynomials -/

set_option maxRecDepth 20000 in
/-- Every certificate polynomial has a nonzero leading coefficient (kernel reduction on the data). -/
theorem polys_ok : ∀ j < 21, polys.getD j [] ≠ [] ∧ (polys.getD j []).headD 0 = 1 := by
  decide +kernel

theorem natDegree_Qc (j : Fin JJ) : (Qc j).natDegree = (polys.getD j []).length - 1 := by
  obtain ⟨hne, hhead⟩ := polys_ok j j.isLt
  unfold Qc
  generalize polys.getD (↑j) [] = l at hne hhead ⊢
  cases l with
  | nil => exact absurd rfl hne
  | cons b t =>
    rw [List.headD_cons] at hhead
    rw [natDegree_Qd_cons (by rw [hhead]; norm_num), List.length_cons, Nat.add_sub_cancel]

theorem Qc_ne_zero (j : Fin JJ) : Qc j ≠ 0 := by
  obtain ⟨hne, hhead⟩ := polys_ok j j.isLt
  unfold Qc
  generalize polys.getD (↑j) [] = l at hne hhead ⊢
  cases l with
  | nil => exact absurd rfl hne
  | cons b t =>
    rw [List.headD_cons] at hhead
    exact Qd_cons_ne_zero (by rw [hhead]; norm_num) t

theorem cR_eq_cj (j : Fin JJ) : cR j = cj j := rfl

theorem cR_nonneg (j : Fin JJ) : 0 ≤ cR j := by
  unfold cR
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

theorem norm_eval_toC_Qc (j : Fin JJ) (x : ℝ) :
    ‖eval (x : ℂ) (toC (Qc j))‖ = |(QR (polys.getD j [])).eval x| := by
  unfold Qc
  exact toC_eval_eq (polys.getD j []) x

theorem leadingCoeff_Qd_cons {b : ℤ} (hb : b ≠ 0) (t : List ℤ) : (Qd (b :: t)).leadingCoeff = b := by
  rw [Qd_cons, leadingCoeff_add_of_degree_lt' (degree_Qd_lt_lead hb t), leadingCoeff_C_mul_X_pow]

theorem Qc_monic (j : Fin JJ) : (Qc j).Monic := by
  obtain ⟨hne, hhead⟩ := polys_ok j j.isLt
  unfold Qc
  generalize polys.getD (↑j) [] = l at hne hhead ⊢
  cases l with
  | nil => exact absurd rfl hne
  | cons b t =>
    rw [List.headD_cons] at hhead
    subst hhead
    exact leadingCoeff_Qd_cons one_ne_zero t

end Trace86.UCert
