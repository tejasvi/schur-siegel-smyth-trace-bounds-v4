import Trace86U.CheckSound4

/-!
# Soundness of the 86a upper checker, part 5: global constants and the polynomial fold of a chord leaf (adapted from the companion Mahler-measure formalization)
-/

open Polynomial

namespace Trace86.UCert

open T86UCore AuxCore AuxCommon

/-! ## Global constants of the context -/

theorem ctx_tab : mkCtx.tab = TAB := rfl
theorem ctx_l2 : mkCtx.l2 = L2 := rfl
theorem ctx_rs : mkCtx.rs = mkRecs := rfl

/-- `m0hi = 0`. -/
theorem m0hi_eq : (mkCtx.m0hi : ℝ) = 0 := by
  show ((0 : ℤ) : ℝ) = 0
  simp

/-- `isLo ≤ 2^P c₀`. -/
theorem isLo_le : (mkCtx.isLo : ℝ) ≤ 2 ^ P * c0R := by
  show ((fdiv ((EPSN : ℤ) * (logT TAB L2 3 2).1) (EPSD - EPSN) : ℤ) : ℝ) ≤ _
  have hD : 0 < EPSD - EPSN := by unfold EPSD EPSN; norm_num
  have hDR : (0 : ℝ) < (EPSD : ℝ) - EPSN := by unfold EPSD EPSN; norm_num
  have hcast : (((EPSD - EPSN : ℕ) : ℝ)) = (EPSD : ℝ) - EPSN := by
    rw [Nat.cast_sub (by unfold EPSD EPSN; norm_num)]
  have h := fdiv_le ((EPSN : ℤ) * (logT TAB L2 3 2).1) hD
  have hl := (logT_sound (a := 3) (b := 2) (by norm_num) (by norm_num)).1
  have hE : (0 : ℝ) ≤ EPSN := Nat.cast_nonneg _
  refine le_trans h ?_
  rw [hcast]
  push_cast
  unfold c0R
  rw [div_le_iff₀ hDR]
  have e : 2 ^ P * ((EPSN : ℝ) * Real.log (3 / 2) / ((EPSD : ℝ) - EPSN)) * ((EPSD : ℝ) - EPSN) =
      (EPSN : ℝ) * (2 ^ P * Real.log (3 / 2)) := by
    field_simp
  rw [e]
  have h32 : ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 3 / 2 := by norm_num
  rw [h32] at hl
  exact mul_le_mul_of_nonneg_left hl hE

theorem logT_D (k : ℕ) :
    ((logT TAB L2 (DEC * 2 ^ k) 1).1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧
      2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ ((logT TAB L2 (DEC * 2 ^ k) 1).2 : ℝ) := by
  have h := logT_sound (a := DEC * 2 ^ k) (b := 1) (Nat.mul_pos (by decide) (Nat.two_pow_pos k)) one_pos
  simpa using h

theorem logT_all : ∀ a b : ℕ, 0 < a → 0 < b → ((logT TAB L2 a b).1 : ℝ) ≤ 2 ^ P * Real.log ((a : ℝ) / b) ∧
    2 ^ P * Real.log ((a : ℝ) / b) ≤ (logT TAB L2 a b).2 := fun a b ha hb => logT_sound ha hb

/-! ## The fold over the polynomials -/

/-- The step of the fold over the polynomials in `chordLB`. -/
def polyFold (g : (List Int × ℕ × ℕ) × ℕ → Option (ℤ × ℤ × ℤ × ℤ × ℤ))
    (acc : Option (ℤ × ℤ × ℤ × ℤ × ℤ)) (x : (List Int × ℕ × ℕ) × ℕ) : Option (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  match acc with
  | none => none
  | some (ap, aq, t0, sl, mp) =>
    match g x with
    | none => none
    | some (ap', aq', t0', sl', mp') => some (ap + ap', aq + aq', t0 + t0', sl + sl', mp + mp')

theorem polyFold_some (g : (List Int × ℕ × ℕ) × ℕ → Option (ℤ × ℤ × ℤ × ℤ × ℤ)) :
    ∀ (L : List ((List Int × ℕ × ℕ) × ℕ)) (s : ℤ × ℤ × ℤ × ℤ × ℤ) (T : ℤ × ℤ × ℤ × ℤ × ℤ),
      L.foldl (polyFold g) (some s) = some T →
        (∀ x ∈ L, (g x).isSome) ∧ T = s + (L.map (fun x => (g x).getD 0)).sum := by
  intro L
  induction L with
  | nil => intro s T h; simp at h; simp [h]
  | cons x L ih =>
    intro s T h
    simp only [List.foldl_cons] at h
    cases hg : g x with
    | none =>
      have : polyFold g (some s) x = none := by simp [polyFold, hg]
      rw [this] at h
      have hn : ∀ L' : List ((List Int × ℕ × ℕ) × ℕ), L'.foldl (polyFold g) none = none := by
        intro L'; induction L' with
        | nil => rfl
        | cons y L' ih' => simp only [List.foldl_cons]; exact ih'
      rw [hn] at h; exact absurd h (by simp)
    | some v =>
      obtain ⟨a1, a2, a3, a4, a5⟩ := s
      obtain ⟨b1, b2, b3, b4, b5⟩ := v
      have : polyFold g (some (a1, a2, a3, a4, a5)) x = some (a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5) := by
        simp [polyFold, hg]
      rw [this] at h
      obtain ⟨h1, h2⟩ := ih _ _ h
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp [hg]
        · exact h1 y hy
      · rw [h2, List.map_cons, List.sum_cons, hg]
        simp only [Option.getD_some]
        rw [← add_assoc]
        rfl

/-- The zipped list of the polynomials, weights and indices. -/
theorem polyList_eq : (List.zip polys (List.zip cwNum cwSh)).zipIdx =
    (List.range 21).map (fun j => ((polys.getD j [], (cwNum.getD j 0, cwSh.getD j 0)), j)) := by
  decide +kernel

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

end Trace86.UCert
