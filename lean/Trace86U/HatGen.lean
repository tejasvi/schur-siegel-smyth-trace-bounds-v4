import T86UCore.Check
import Mathlib.Tactic

/-!
# The slope jumps of a sum of hats (list lemmas for the checker's `hatC`)

`hatC rs ns rho` lists the exact slope jumps `C_0, …, C_N` (`N = rho.length + 1`) of `∑_j ρ_j h_j` as fractions:
`(hatC rs ns rho)[i] = L_{i+1} + M_i + R_{i-1}`, where the hat at node `j` (`0 < j < N`) has weight `rho[j-1]` and
gaps `ns[j] - ns[j-1]`, `ns[j+1] - ns[j]` (`hatC_getElem`).
-/

namespace Trace86.UCert

open T86UCore

/-- The gap `n_j - n_{j-1}`. -/
def gapL (ns : List ℕ) (j : ℕ) : ℕ := ns.getD j 0 - ns.getD (j - 1) 0

/-- The contribution `f` (`hatL`, `hatM` or `hatR`) of the hat at node `j`; zero unless `0 < j < rho.length + 1`. -/
def hatAt (f : ℕ → ℕ → ℕ → ℕ → ℤ × ℕ) (rs : ℕ) (ns rho : List ℕ) (j : ℕ) : ℤ × ℕ :=
  if 0 < j ∧ j < rho.length + 1 then f rs (rho.getD (j - 1) 0) (gapL ns j) (gapL ns (j + 1)) else (0, 1)

theorem gaps_length : ∀ l : List ℕ, (gaps l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [gaps, List.length_cons, gaps_length (b :: t)]
    omega

theorem gaps_getElem : ∀ (l : List ℕ) (k : ℕ) (hk : k < (gaps l).length), (gaps l)[k] = gapL l (k + 1)
  | [], k, hk => by simp [gaps] at hk
  | [_], k, hk => by simp [gaps] at hk
  | a :: b :: t, 0, _ => by simp [gaps, gapL]
  | a :: b :: t, k + 1, hk => by
    simp only [gaps, List.getElem_cons_succ]
    rw [gaps_getElem (b :: t) k (by simp only [gaps, List.length_cons] at hk; omega)]
    simp [gapL]

/-- The hat triples `(ρ_j, a_j, b_j)`, `j = k + 1`. -/
def tripL (ns rho : List ℕ) : List (ℕ × ℕ × ℕ) := List.zip rho (List.zip (gaps ns) ((gaps ns).drop 1))

def LsL (rs : ℕ) (ns rho : List ℕ) : List (ℤ × ℕ) :=
  (tripL ns rho).map (fun t => hatL rs t.1 t.2.1 t.2.2) ++ [(0, 1), (0, 1)]

def MsL (rs : ℕ) (ns rho : List ℕ) : List (ℤ × ℕ) :=
  (0, 1) :: ((tripL ns rho).map (fun t => hatM rs t.1 t.2.1 t.2.2) ++ [(0, 1)])

def RsL (rs : ℕ) (ns rho : List ℕ) : List (ℤ × ℕ) :=
  (0, 1) :: (0, 1) :: (tripL ns rho).map (fun t => hatR rs t.1 t.2.1 t.2.2)

theorem hatC_eq (rs : ℕ) (ns rho : List ℕ) :
    hatC rs ns rho = List.zipWith qadd (List.zipWith qadd (LsL rs ns rho) (MsL rs ns rho)) (RsL rs ns rho) := rfl

section

variable {rs : ℕ} {ns rho : List ℕ}

theorem tripL_length (h : ns.length = rho.length + 2) : (tripL ns rho).length = rho.length := by
  have hg : (gaps ns).length = rho.length + 1 := by rw [gaps_length, h]; omega
  simp only [tripL, List.length_zip, List.length_drop, hg]
  omega

theorem tripL_getElem (h : ns.length = rho.length + 2) (k : ℕ) (hk : k < (tripL ns rho).length) :
    (tripL ns rho)[k] = (rho.getD k 0, gapL ns (k + 1), gapL ns (k + 2)) := by
  have hk' : k < rho.length := by rw [tripL_length h] at hk; exact hk
  simp only [tripL, List.getElem_zip, List.getElem_drop, gaps_getElem]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some,
    show 1 + k + 1 = k + 2 by omega]

theorem getElem_pair {α : Type*} (a : α) (m : ℕ) (hm : m < [a, a].length) : [a, a][m] = a := by
  match m, hm with
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, hm => exact absurd hm (by simp)

theorem LsL_length (h : ns.length = rho.length + 2) : (LsL rs ns rho).length = rho.length + 2 := by
  simp [LsL, tripL_length h]

theorem MsL_length (h : ns.length = rho.length + 2) : (MsL rs ns rho).length = rho.length + 2 := by
  simp [MsL, tripL_length h]

theorem RsL_length (h : ns.length = rho.length + 2) : (RsL rs ns rho).length = rho.length + 2 := by
  simp [RsL, tripL_length h]

theorem LsL_getElem (h : ns.length = rho.length + 2) (i : ℕ) (hi : i < (LsL rs ns rho).length) :
    (LsL rs ns rho)[i] = hatAt hatL rs ns rho (i + 1) := by
  have hl := tripL_length h
  simp only [LsL]
  unfold hatAt
  by_cases hA : i < rho.length
  · rw [List.getElem_append_left (by simp [hl, hA]), List.getElem_map, tripL_getElem h,
      if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  · rw [List.getElem_append_right (by simp [hl]; omega), getElem_pair, if_neg (by omega)]

theorem MsL_getElem (h : ns.length = rho.length + 2) (i : ℕ) (hi : i < (MsL rs ns rho).length) :
    (MsL rs ns rho)[i] = hatAt hatM rs ns rho i := by
  have hl := tripL_length h
  simp only [MsL]
  unfold hatAt
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [List.getElem_cons_zero, if_neg (by omega)]
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [List.getElem_cons_succ]
    by_cases hB : m < rho.length
    · rw [List.getElem_append_left (by simp [hl, hB]), List.getElem_map, tripL_getElem h,
        if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    · rw [List.getElem_append_right (by simp [hl]; omega), List.getElem_singleton, if_neg (by omega)]

theorem RsL_getElem (h : ns.length = rho.length + 2) (i : ℕ) (hi : i < (RsL rs ns rho).length) :
    (RsL rs ns rho)[i] = hatAt hatR rs ns rho (i - 1) := by
  have hl := tripL_length h
  have hi' : i < rho.length + 2 := by rw [RsL_length h] at hi; exact hi
  simp only [RsL]
  unfold hatAt
  match i, hi, hi' with
  | 0, _, _ => rw [List.getElem_cons_zero, if_neg (by omega)]
  | 1, _, _ => rw [List.getElem_cons_succ, List.getElem_cons_zero, if_neg (by omega)]
  | m + 2, _, hm =>
    rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_map, tripL_getElem h,
      if_pos ⟨by omega, by omega⟩]
    simp only [show m + 2 - 1 - 1 = m by omega, show m + 2 - 1 = m + 1 by omega]
    rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega]

theorem hatC_length (h : ns.length = rho.length + 2) : (hatC rs ns rho).length = rho.length + 2 := by
  rw [hatC_eq]
  simp [LsL_length h, MsL_length h, RsL_length h]

/-- **The checker's slope jumps**: `C_i = L_{i+1} + M_i + R_{i-1}`. -/
theorem hatC_getElem (h : ns.length = rho.length + 2) (i : ℕ) (hi : i < (hatC rs ns rho).length) :
    (hatC rs ns rho)[i] =
      qadd (qadd (hatAt hatL rs ns rho (i + 1)) (hatAt hatM rs ns rho i)) (hatAt hatR rs ns rho (i - 1)) := by
  simp only [hatC_eq, List.getElem_zipWith, LsL_getElem h, MsL_getElem h, RsL_getElem h]

end

end Trace86.UCert
