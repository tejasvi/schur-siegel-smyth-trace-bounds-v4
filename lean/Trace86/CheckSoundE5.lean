import Trace86.CheckSoundE4

/-!
# Soundness of the end-point form, part 5: leaves and tilings (`leafOKE`, `leavesOKE`)

The same statements as `leafOK_sound` and `leavesOK_sound` (`Trace86.CheckSound10`), for the checker in end-point form.
-/

open Polynomial Set

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

/-- A passing chord leaf has `Xp < Xq`. -/
theorem chordLBC_lt {c : Ctx} {A B : EPt} {Xp Xq k : ℕ} {x0q : Bool} {mask : ℕ} {v : ℤ × ℤ}
    (h : chordLBC c A B Xp Xq k x0q mask = some v) : Xp < Xq := by
  by_contra hlt
  unfold chordLBC at h
  dsimp only at h
  rw [if_neg (fun hc => hlt hc.1)] at h
  exact absurd h (by simp)

/-- **One leaf.** -/
theorem leafOKE_sound (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) {l : Leaf} (h : leafOKE (mkCtx iLoNum 128) l = true) :
    (l.X1 : ℝ) / (DEC * 2 ^ l.k : ℕ) < (l.X2 : ℝ) / (DEC * 2 ^ l.k : ℕ) ∧
    ∀ x ∈ Icc ((l.X1 : ℝ) / (DEC * 2 ^ l.k : ℕ)) ((l.X2 : ℝ) / (DEC * 2 ^ l.k : ℕ)),
      (∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) → 0 < FR x := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hD := DEC_pow_pos l.k
  unfold leafOKE at h
  split_ifs at h with hk
  · unfold chordOKC at h
    rcases hc : chordLBC (mkCtx iLoNum 128) (epAt (mkCtx iLoNum 128) l.X1 l.k) (epAt (mkCtx iLoNum 128) l.X2 l.k)
        l.X1 l.X2 l.k l.x0q l.mask with _ | ⟨lp, lq⟩
    · rw [hc] at h; exact absurd h (by simp)
    · rw [hc] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hlt := chordLBC_lt hc
      refine ⟨div_lt_div_of_pos_right (by exact_mod_cast hlt) hD, ?_⟩
      intro x hx _
      have h1 := chordLBC_sound hI hc x hx
      have h2 : (0 : ℝ) < min (lp : ℝ) lq := lt_min (by exact_mod_cast h.1) (by exact_mod_cast h.2)
      have h3 : 0 < min (lp : ℝ) lq / 2 ^ P := div_pos h2 hP
      linarith
  · unfold windowOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨huv, hv22⟩, hpos⟩ := h
    have hv : (l.X2 : ℝ) / (DEC * 2 ^ l.k : ℕ) ≤ 22 := by
      rw [div_le_iff₀ hD]
      exact_mod_cast hv22
    refine ⟨div_lt_div_of_pos_right (by exact_mod_cast huv) hD, ?_⟩
    intro x hx hQ
    have h1 := windowLB_sound hI huv hv hx hQ
    have h3 : 0 < (windowLB (mkCtx iLoNum 128) l.X1 l.X2 l.k : ℝ) / 2 ^ P :=
      div_pos (by exact_mod_cast hpos) hP
    linarith

/-- **The tiling.** -/
theorem leavesOKE_sound (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) : ∀ (ls : List Leaf) (X kx XT kT : ℕ),
    leavesOKE (mkCtx iLoNum 128) X kx ls XT kT = true →
    (X : ℝ) / (DEC * 2 ^ kx : ℕ) ≤ (XT : ℝ) / (DEC * 2 ^ kT : ℕ) ∧
    ∀ x ∈ Ico ((X : ℝ) / (DEC * 2 ^ kx : ℕ)) ((XT : ℝ) / (DEC * 2 ^ kT : ℕ)),
      (∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) → 0 < FR x
  | [], X, kx, XT, kT, h => by
    simp only [leavesOKE] at h
    have he := ptEq_real h
    refine ⟨he.le, ?_⟩
    intro x hx
    rw [he] at hx
    exact absurd hx.2 (not_lt.mpr hx.1)
  | l :: ls, X, kx, XT, kT, h => by
    simp only [leavesOKE, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hle, hrest⟩ := leavesOKE_sound hI ls l.X2 l.k XT kT h3
    obtain ⟨hlt, hleaf⟩ := leafOKE_sound hI h2
    have he := ptEq_real h1
    refine ⟨by rw [he]; linarith, ?_⟩
    intro x hx hQ
    rw [he] at hx
    by_cases hxl : x ≤ (l.X2 : ℝ) / (DEC * 2 ^ l.k : ℕ)
    · exact hleaf x ⟨hx.1, hxl⟩ hQ
    · exact hrest x ⟨le_of_lt (not_le.mp hxl), hx.2⟩ hQ

/-- Changing the start point of a tiling to an equal point. -/
theorem leavesOKE_start {c : Ctx} {X kx Y ky : ℕ} (hXY : ptEq X kx Y ky = true) :
    ∀ (ls : List Leaf) (XT kT : ℕ), leavesOKE c Y ky ls XT kT = true → leavesOKE c X kx ls XT kT = true
  | [], XT, kT, h => by
    simp only [leavesOKE] at h ⊢
    exact ptEq_trans hXY h
  | l :: ls, XT, kT, h => by
    simp only [leavesOKE, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ptEq_trans hXY h.1.1, h.1.2⟩, h.2⟩

theorem leavesOKE_append (c : Ctx) : ∀ (l1 l2 : List Leaf) (X kx Y ky XT kT : ℕ),
    leavesOKE c X kx l1 Y ky = true → leavesOKE c Y ky l2 XT kT = true → leavesOKE c X kx (l1 ++ l2) XT kT = true
  | [], l2, X, kx, Y, ky, XT, kT, h1, h2 => by
    simp only [leavesOKE] at h1
    exact leavesOKE_start h1 l2 XT kT h2
  | l :: ls, l2, X, kx, Y, ky, XT, kT, h1, h2 => by
    simp only [leavesOKE, Bool.and_eq_true, List.cons_append] at h1 ⊢
    exact ⟨h1.1, leavesOKE_append c ls l2 l.X2 l.k Y ky XT kT h1.2 h2⟩

theorem take_append_drop_E (l : List Leaf) (a n : ℕ) : (l.drop a).take n ++ l.drop (a + n) = l.drop a := by
  have h := List.take_append_drop n (l.drop a)
  rwa [List.drop_drop] at h

/-- Composition of the checks of consecutive pieces of the leaf list. -/
theorem chunk_stepE {c : Ctx} {X kx Y ky XT kT a n : ℕ}
    (h1 : leavesOKE c X kx ((leaves.drop a).take n) Y ky = true)
    (h2 : leavesOKE c Y ky (leaves.drop (a + n)) XT kT = true) :
    leavesOKE c X kx (leaves.drop a) XT kT = true := by
  have h := leavesOKE_append c _ _ X kx Y ky XT kT h1 h2
  rwa [take_append_drop_E] at h

theorem take_stepE {c : Ctx} {X kx Y ky Z kz a n m t b : ℕ} (ht : n + m = t) (hb : a + n = b)
    (h1 : leavesOKE c X kx ((leaves.drop a).take n) Y ky = true)
    (h2 : leavesOKE c Y ky ((leaves.drop b).take m) Z kz = true) :
    leavesOKE c X kx ((leaves.drop a).take t) Z kz = true := by
  subst ht hb
  rw [List.take_add, List.drop_drop]
  exact leavesOKE_append c _ _ X kx Y ky Z kz h1 h2

end Trace86.Cert
