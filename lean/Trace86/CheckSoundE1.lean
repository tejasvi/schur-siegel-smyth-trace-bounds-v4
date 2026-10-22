import Trace86.CheckSound10
import T86Core.CheckE

/-!
# Soundness of the end-point form, part 1: the end-point pass (`epData`)

For `x = X / D`, `D = 10^12 2^k`: `uhi ≥ 2^P U(x)`, `g0 ≤ 2^(P+QS) ∑_{e_i ≠ x} C_i log |x - e_i|`, `kl`, `kr` bound
`2^QS ∑ 2 |C_i| / (x - e_i)²` over the nodes with `C_i < 0` left resp. right of `x`, `cl`, `cle` count the nodes with
`C_i ≠ 0` and `e_i < x` resp. `e_i ≤ x`, and `apl, aph` (`anl, anh`) enclose `2^QS ∑ C_i` over the nodes at `x` with
`C_i > 0` (`C_i < 0`).
-/

open Polynomial Set

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

/-! ### Reduced points -/

theorem canon_spec : ∀ (k X : ℕ), (canon X k).2 ≤ k ∧ (canon X k).1 * 2 ^ (k - (canon X k).2) = X
  | 0, X => by simp [canon]
  | k + 1, X => by
    unfold canon
    split_ifs with h
    · obtain ⟨h1, h2⟩ := canon_spec k (X / 2)
      refine ⟨by omega, ?_⟩
      rw [show k + 1 - (canon (X / 2) k).2 = (k - (canon (X / 2) k).2) + 1 by omega, pow_succ, ← mul_assoc, h2]
      omega
    · simp

theorem canon_real (X k : ℕ) :
    ((canon X k).1 : ℝ) / ((DEC * 2 ^ (canon X k).2 : ℕ) : ℝ) = (X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := canon_spec k X
  set a := (canon X k).1 with ha
  set b := (canon X k).2 with hb
  have e : (2 : ℝ) ^ k = 2 ^ b * 2 ^ (k - b) := by
    rw [← pow_add]; congr 1; omega
  have hX : (X : ℝ) = (a : ℝ) * 2 ^ (k - b) := by
    rw [← h2]; push_cast; ring
  rw [hX]
  push_cast
  rw [e]
  have h2p : (0 : ℝ) < 2 ^ (k - b) := by positivity
  have hD : (0 : ℝ) < (DEC : ℝ) * 2 ^ b := by unfold DEC; positivity
  field_simp

/-- The node `i` and the point `X / (10^12 2^k)`. -/
theorem eR_sub_pt (i k X : ℕ) :
    eR i - (X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) = (((nodes.getD i 0 * 2 ^ k : ℕ) : ℝ) - X) / ((DEC * 2 ^ k : ℕ) : ℝ) := by
  rw [eR_sub_x]; push_cast; ring

theorem eR_eq_pt_iff (i k X : ℕ) : eR i = (X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) ↔ nodes.getD i 0 * 2 ^ k = X := by
  have hD : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := DEC_pow_pos k
  rw [← sub_eq_zero, eR_sub_pt, div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h hD.ne'
  · intro h; left; exact_mod_cast h

theorem eR_lt_pt_iff (i k X : ℕ) : eR i < (X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) ↔ nodes.getD i 0 * 2 ^ k < X := by
  have hD : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := DEC_pow_pos k
  rw [← sub_neg, eR_sub_pt, div_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
    · exact absurd h (not_lt.mpr hD.le)
    · have : ((nodes.getD i 0 * 2 ^ k : ℕ) : ℝ) < X := by linarith
      exact_mod_cast this
  · intro h
    right
    have : ((nodes.getD i 0 * 2 ^ k : ℕ) : ℝ) < X := by exact_mod_cast h
    exact ⟨by linarith, hD⟩

theorem pt_lt_eR_iff (i k X : ℕ) : (X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ) < eR i ↔ X < nodes.getD i 0 * 2 ^ k := by
  have h1 := eR_eq_pt_iff i k X
  have h2 := eR_lt_pt_iff i k X
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rcases Nat.lt_or_eq_of_le hc with h3 | h3
    · linarith [h2.mpr h3]
    · linarith [h1.mpr h3]
  · intro h
    rcases lt_trichotomy (eR i) ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) with h3 | h3 | h3
    · have := h2.mp h3; omega
    · have := h1.mp h3; omega
    · exact h3

/-! ### One node of the end-point pass -/

/-- The fields of the end-point pass other than the U-sum. -/
noncomputable def gT (x : ℝ) (i : ℕ) : ℝ := if eR i = x then 0 else CR i * Real.log |x - eR i|
noncomputable def klT (x : ℝ) (i : ℕ) : ℝ := if CR i < 0 ∧ eR i < x then 2 * |CR i| / (x - eR i) ^ 2 else 0
noncomputable def krT (x : ℝ) (i : ℕ) : ℝ := if CR i < 0 ∧ x < eR i then 2 * |CR i| / (x - eR i) ^ 2 else 0
noncomputable def clT (x : ℝ) (i : ℕ) : ℕ := if CR i ≠ 0 ∧ eR i < x then 1 else 0
noncomputable def cleT (x : ℝ) (i : ℕ) : ℕ := if CR i ≠ 0 ∧ eR i ≤ x then 1 else 0
noncomputable def apT (x : ℝ) (i : ℕ) : ℝ := if eR i = x ∧ 0 < CR i then CR i else 0
noncomputable def anT (x : ℝ) (i : ℕ) : ℝ := if eR i = x ∧ CR i < 0 then CR i else 0

theorem epStep_s (tab : ℕ) (l2 : ℕ × ℕ) (k X : ℕ) (DD : ℤ) (LD : ℤ × ℤ) (a : EAcc) (r : NRec) :
    (epStep tab l2 k X DD LD a r).s = pointStep tab l2 k X LD a.s r := by
  unfold epStep pointStep
  by_cases h0 : r.sg = 0
  · simp [h0]
  · by_cases hX : r.n * 2 ^ k = X
    · have had : (if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k) = 0 := by split_ifs <;> omega
      by_cases hs : 0 < r.sg <;> simp [h0, hX, had, hs]
    · have had : (if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k) ≠ 0 := by split_ifs <;> omega
      by_cases hl : r.n * 2 ^ k < X <;> simp [h0, hX, had, hl]

theorem epPass_s (tab : ℕ) (l2 : ℕ × ℕ) (k X : ℕ) (DD : ℤ) (LD : ℤ × ℤ) :
    ∀ (rs : List NRec) (a : EAcc),
      (rs.foldl (epStep tab l2 k X DD LD) a).s = rs.foldl (pointStep tab l2 k X LD) a.s
  | [], _ => rfl
  | r :: rs, a => by
    simp only [List.foldl_cons]
    rw [epPass_s tab l2 k X DD LD rs, epStep_s]

theorem epStep_zero (tab : ℕ) (l2 : ℕ × ℕ) (k X : ℕ) (DD : ℤ) (LD : ℤ × ℤ) (a : EAcc) (r : NRec) (hs : r.sg = 0) :
    epStep tab l2 k X DD LD a r = a := by
  simp [epStep, hs]

theorem epStep_at (tab : ℕ) (l2 : ℕ × ℕ) (k X : ℕ) (DD : ℤ) (LD : ℤ × ℤ) (a : EAcc) (r : NRec) (hs : r.sg ≠ 0)
    (hX : r.n * 2 ^ k = X) :
    (epStep tab l2 k X DD LD a r).g0 = a.g0 ∧ (epStep tab l2 k X DD LD a r).kl = a.kl ∧
    (epStep tab l2 k X DD LD a r).kr = a.kr ∧ (epStep tab l2 k X DD LD a r).cl = a.cl ∧
    (epStep tab l2 k X DD LD a r).cle = a.cle + 1 ∧
    (epStep tab l2 k X DD LD a r).apl = a.apl + (if 0 < r.sg then r.clo else 0) ∧
    (epStep tab l2 k X DD LD a r).aph = a.aph + (if 0 < r.sg then r.chi else 0) ∧
    (epStep tab l2 k X DD LD a r).anl = a.anl + (if 0 < r.sg then 0 else r.clo) ∧
    (epStep tab l2 k X DD LD a r).anh = a.anh + (if 0 < r.sg then 0 else r.chi) := by
  by_cases hp : 0 < r.sg <;> simp [epStep, hs, hX, hp]

theorem epStep_away (tab : ℕ) (l2 : ℕ × ℕ) (k X : ℕ) (DD : ℤ) (LD : ℤ × ℤ) (a : EAcc) (r : NRec) (hs : r.sg ≠ 0)
    (hX : r.n * 2 ^ k ≠ X) :
    (epStep tab l2 k X DD LD a r).g0 = a.g0 + (imul (r.clo, r.chi)
      ((logT tab l2 (if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k) 1).1 - LD.2,
       (logT tab l2 (if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k) 1).2 - LD.1)).1 ∧
    (epStep tab l2 k X DD LD a r).kl = a.kl + (if r.n * 2 ^ k < X then
      (if r.sg < 0 then cdiv (2 * (-r.clo) * DD) ((if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k) *
        (if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k)) else 0) else 0) ∧
    (epStep tab l2 k X DD LD a r).kr = a.kr + (if r.n * 2 ^ k < X then 0 else
      (if r.sg < 0 then cdiv (2 * (-r.clo) * DD) ((if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k) *
        (if X ≤ r.n * 2 ^ k then r.n * 2 ^ k - X else X - r.n * 2 ^ k)) else 0)) ∧
    (epStep tab l2 k X DD LD a r).cl = a.cl + (if r.n * 2 ^ k < X then 1 else 0) ∧
    (epStep tab l2 k X DD LD a r).cle = a.cle + (if r.n * 2 ^ k < X then 1 else 0) ∧
    (epStep tab l2 k X DD LD a r).apl = a.apl ∧ (epStep tab l2 k X DD LD a r).aph = a.aph ∧
    (epStep tab l2 k X DD LD a r).anl = a.anl ∧ (epStep tab l2 k X DD LD a r).anh = a.anh := by
  by_cases hl : r.n * 2 ^ k < X <;> simp [epStep, hs, hX, hl]

theorem epStep_spec {k X i : ℕ} (hi : i ≤ NN) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ LD.2)
    (a : EAcc) :
    ((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).g0 : ℝ) - a.g0 ≤
      2 ^ (P + QS) * gT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
    2 ^ QS * klT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
      ((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).kl : ℝ) - a.kl ∧
    2 ^ QS * krT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
      ((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).kr : ℝ) - a.kr ∧
    (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).cl =
      a.cl + clT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
    (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).cle =
      a.cle + cleT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
    (((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).apl : ℝ) - a.apl ≤
        2 ^ QS * apT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      2 ^ QS * apT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
        ((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).aph : ℝ) - a.aph) ∧
    (((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).anl : ℝ) - a.anl ≤
        2 ^ QS * anT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      2 ^ QS * anT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
        ((epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD a (recOf i)).anh : ℝ) - a.anh) := by
  set D : ℕ := DEC * 2 ^ k with hDdef
  set x : ℝ := (X : ℝ) / (D : ℝ) with hxdef
  set a' := epStep TAB L2 k X ((D * D : ℕ) : ℤ) LD a (recOf i) with ha'def
  obtain ⟨hclo, hchi, hsg0, hsgpos, hn⟩ := recOf_spec hi
  have hD : 0 < D := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hPQ : (2 : ℝ) ^ (P + QS) = 2 ^ P * 2 ^ QS := pow_add 2 P QS
  have hQ : (0 : ℝ) < 2 ^ QS := by positivity
  set ni : ℕ := nodes.getD i 0 * 2 ^ k with hni
  have heq : eR i = x ↔ ni = X := eR_eq_pt_iff i k X
  have hlt : eR i < x ↔ ni < X := eR_lt_pt_iff i k X
  have hgt : x < eR i ↔ X < ni := pt_lt_eR_iff i k X
  have hrn : (recOf i).n * 2 ^ k = ni := by rw [hn]
  by_cases hs : (recOf i).sg = 0
  · -- `C_i = 0`: nothing changes
    have hC : CR i = 0 := hsg0.mp hs
    rw [ha'def, epStep_zero _ _ _ _ _ _ _ _ hs]
    simp [gT, klT, krT, clT, cleT, apT, anT, hC]
  · have hC : CR i ≠ 0 := fun h => hs (hsg0.mpr h)
    by_cases hX : ni = X
    · -- the node is at `x`
      have hex : eR i = x := heq.mpr hX
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ :=
        epStep_at TAB L2 k X ((D * D : ℕ) : ℤ) LD a (recOf i) hs (by rw [hrn]; exact hX)
      rw [← ha'def] at e1 e2 e3 e4 e5 e6 e7 e8 e9
      have hT : gT x i = 0 ∧ klT x i = 0 ∧ krT x i = 0 ∧ clT x i = 0 ∧ cleT x i = 1 := by
        simp [gT, klT, krT, clT, cleT, hex, hC]
      obtain ⟨t1, t2, t3, t4, t5⟩ := hT
      rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, t1, t2, t3, t4, t5]
      by_cases hp : 0 < (recOf i).sg
      · have hCp : 0 < CR i := hsgpos.mp hp
        have ha : apT x i = CR i := by simp [apT, hex, hCp]
        have hb : anT x i = 0 := by simp [anT, hex, not_lt.mpr hCp.le]
        rw [ha, hb]
        simp only [hp, if_true]
        push_cast
        refine ⟨by simp, by simp, by simp, by simp, by simp, ⟨by linarith, by linarith⟩, by simp⟩
      · have hCn : CR i < 0 := lt_of_le_of_ne (not_lt.mp (fun h => hp (hsgpos.mpr h))) hC
        have ha : apT x i = 0 := by simp [apT, hex, not_lt.mpr hCn.le]
        have hb : anT x i = CR i := by simp [anT, hex, hCn]
        rw [ha, hb]
        simp only [hp, if_false]
        push_cast
        refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, ⟨by linarith, by linarith⟩⟩
    · -- a node away from `x`
      have hne : eR i ≠ x := fun h => hX (heq.mp h)
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ :=
        epStep_away TAB L2 k X ((D * D : ℕ) : ℤ) LD a (recOf i) hs (by rw [hrn]; exact hX)
      rw [← ha'def] at e1 e2 e3 e4 e5 e6 e7 e8 e9
      rw [hrn] at e1 e2 e3 e4 e5
      set ad : ℕ := if X ≤ ni then ni - X else X - ni with hadef
      have hadpos : 0 < ad := by rw [hadef]; split_ifs <;> omega
      have hadR : (ad : ℝ) = |(nodes.getD i 0 : ℝ) * 2 ^ k - X| := dist_cast _ _ _
      have habs : |x - eR i| = ad / D := by
        rw [abs_sub_comm, show eR i - x = ((nodes.getD i 0 : ℝ) * 2 ^ k - X) / D from eR_sub_x i k X, abs_div,
          abs_of_pos hDR, hadR]
      have hxe : (x - eR i) ^ 2 = (ad : ℝ) ^ 2 / (D : ℝ) ^ 2 := by rw [← sq_abs, habs, div_pow]
      set L := logT TAB L2 ad 1 with hL
      obtain ⟨hL1, hL2⟩ := logT_sound (a := ad) (b := 1) hadpos one_pos
      simp only [Nat.cast_one, div_one] at hL1 hL2
      have hlog : Real.log |x - eR i| = Real.log ad - Real.log D := by
        rw [habs, Real.log_div (by exact_mod_cast hadpos.ne') hDR.ne']
      have hv : (((L.1 - LD.2, L.2 - LD.1) : ℤ × ℤ).1 : ℝ) ≤ 2 ^ P * Real.log |x - eR i| ∧
          2 ^ P * Real.log |x - eR i| ≤ (((L.1 - LD.2, L.2 - LD.1) : ℤ × ℤ).2 : ℝ) := by
        simp only
        rw [hlog]; push_cast
        constructor <;> nlinarith [hLD.1, hLD.2]
      have hc : (((recOf i).clo, (recOf i).chi).1 : ℝ) ≤ 2 ^ QS * CR i ∧
          2 ^ QS * CR i ≤ (((recOf i).clo, (recOf i).chi).2 : ℝ) := ⟨hclo, hchi⟩
      have hg := imul_spec hc hv
      -- the `K` term
      set kt : ℤ := if (recOf i).sg < 0 then cdiv (2 * (-(recOf i).clo) * ((D * D : ℕ) : ℤ)) (ad * ad) else 0
        with hktdef
      have hkt : CR i < 0 → 2 ^ QS * (2 * |CR i| / (x - eR i) ^ 2) ≤ (kt : ℝ) := by
        intro hCn
        have hsn : (recOf i).sg < 0 := by
          rcases lt_trichotomy (recOf i).sg 0 with h | h | h
          · exact h
          · exact absurd h hs
          · exact absurd (hsgpos.mp h) (not_lt.mpr hCn.le)
        have hden : 0 < ad * ad := Nat.mul_pos hadpos hadpos
        have h1 := le_cdiv (2 * (-(recOf i).clo) * ((D * D : ℕ) : ℤ)) hden
        rw [hktdef, if_pos hsn]
        refine le_trans ?_ h1
        rw [hxe, abs_of_neg hCn]
        push_cast
        have hadR' : (0 : ℝ) < ad := by exact_mod_cast hadpos
        have e : 2 ^ QS * (2 * -CR i / ((ad : ℝ) ^ 2 / (D : ℝ) ^ 2)) =
            (2 * (2 ^ QS * -CR i) * ((D : ℝ) * D)) / ((ad : ℝ) * ad) := by
          field_simp
        rw [e, div_le_div_iff_of_pos_right (by positivity)]
        have hcl : 2 ^ QS * -CR i ≤ -((recOf i).clo : ℝ) := by linarith
        nlinarith [mul_pos hDR hDR]
      have hkt0 : ¬ CR i < 0 → kt = 0 := by
        intro hCn
        rw [hktdef, if_neg]
        intro hsn
        exact hCn (by
          rcases lt_or_gt_of_ne hC with h | h
          · exact h
          · exact absurd (hsgpos.mpr h) (not_lt.mpr hsn.le))
      have hgT : gT x i = CR i * Real.log |x - eR i| := by simp [gT, hne]
      have hapT : apT x i = 0 := by simp [apT, hne]
      have hanT : anT x i = 0 := by simp [anT, hne]
      rw [hgT, hapT, hanT, e1, e6, e7, e8, e9]
      have hg0 : ((a.g0 + (imul ((recOf i).clo, (recOf i).chi) (L.1 - LD.2, L.2 - LD.1)).1 : ℤ) : ℝ) - a.g0 ≤
          2 ^ (P + QS) * (CR i * Real.log |x - eR i|) := by
        push_cast
        have : (2 : ℝ) ^ (P + QS) * (CR i * Real.log |x - eR i|) =
            (2 ^ QS * CR i) * (2 ^ P * Real.log |x - eR i|) := by rw [hPQ]; ring
        rw [this]; linarith [hg.1]
      by_cases hl : ni < X
      · have hel : eR i < x := hlt.mpr hl
        have hng : ¬ x < eR i := not_lt.mpr hel.le
        rw [if_pos hl] at e2 e3 e4 e5
        rw [e2, e3, e4, e5]
        have hcl : clT x i = 1 := by simp [clT, hC, hel]
        have hcle : cleT x i = 1 := by simp [cleT, hC, hel.le]
        have hkr : krT x i = 0 := by simp [krT, hng]
        rw [hcl, hcle, hkr]
        refine ⟨hg0, ?_, by simp, rfl, rfl, by simp, by simp⟩
        push_cast
        by_cases hCn : CR i < 0
        · simp only [klT, hCn, hel, and_self, if_true]
          linarith [hkt hCn]
        · simp only [klT, hCn, false_and, if_false, mul_zero]
          rw [hkt0 hCn]; simp
      · have hgt' : X < ni := by omega
        have heg : x < eR i := hgt.mpr hgt'
        have hnl' : ¬ eR i < x := not_lt.mpr heg.le
        rw [if_neg hl] at e2 e3 e4 e5
        rw [e2, e3, e4, e5]
        have hcl : clT x i = 0 := by simp [clT, hnl']
        have hcle : cleT x i = 0 := by simp [cleT, not_le.mpr heg]
        have hkl : klT x i = 0 := by simp [klT, hnl']
        rw [hcl, hcle, hkl]
        refine ⟨hg0, by simp, ?_, by simp, by simp, by simp, by simp⟩
        push_cast
        by_cases hCn : CR i < 0
        · simp only [krT, hCn, heg, and_self, if_true]
          linarith [hkt hCn]
        · simp only [krT, hCn, false_and, if_false, mul_zero]
          rw [hkt0 hCn]; simp

/-! ### The end-point pass over all nodes -/

theorem epPass_range {k X : ℕ} {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ LD.2) :
    ∀ n ≤ NN + 1,
      ((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).g0 : ℝ) ≤
        2 ^ (P + QS) * ∑ i ∈ Finset.range n, gT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      2 ^ QS * ∑ i ∈ Finset.range n, klT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
        ((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).kl : ℝ) ∧
      2 ^ QS * ∑ i ∈ Finset.range n, krT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
        ((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).kr : ℝ) ∧
      (((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).cl =
        ∑ i ∈ Finset.range n, clT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      (((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).cle =
        ∑ i ∈ Finset.range n, cleT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      (((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).apl : ℝ) ≤
          2 ^ QS * ∑ i ∈ Finset.range n, apT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
        2 ^ QS * ∑ i ∈ Finset.range n, apT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
          ((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).aph : ℝ)) ∧
      (((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).anl : ℝ) ≤
          2 ^ QS * ∑ i ∈ Finset.range n, anT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
        2 ^ QS * ∑ i ∈ Finset.range n, anT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤
          ((((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero).anh : ℝ)) := by
  intro n
  induction n with
  | zero => intro _; simp [epZero]
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2, i3, i4, i5, ⟨i6, i7⟩, ⟨i8, i9⟩⟩ := ih (by omega)
    obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, ⟨h8, h9⟩⟩ := epStep_spec (k := k) (X := X) (i := n) (by omega) hLD
      (((List.range n).map recOf).foldl (epStep TAB L2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : ℕ) : ℤ) LD) epZero)
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Finset.sum_range_succ, mul_add]
    refine ⟨by linarith, by linarith, by linarith, by rw [h4, i4], by rw [h5, i5], ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩

theorem epData_eq (kc Xc : ℕ) : epData (mkCtx iLoNum 128) kc Xc =
    ⟨uHi (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).s (DEC * 2 ^ kc),
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).g0,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).kl,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).kr,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).cl,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).cle,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).apl,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).aph,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).anl,
      (((List.range (NN + 1)).map recOf).foldl (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ)
        (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).anh⟩ := by
  unfold epData
  rw [ctx_rs, ctx_tab, ctx_l2, mkRecs_eq]

theorem epData_spec (kc Xc : ℕ) :
    2 ^ P * UR ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) ≤ ((epData (mkCtx iLoNum 128) kc Xc).uhi : ℝ) ∧
    ((epData (mkCtx iLoNum 128) kc Xc).g0 : ℝ) ≤ 2 ^ (P + QS) * ∑ i ∈ Finset.range (NN + 1), gT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ∧
    2 ^ QS * ∑ i ∈ Finset.range (NN + 1), klT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ≤ ((epData (mkCtx iLoNum 128) kc Xc).kl : ℝ) ∧
    2 ^ QS * ∑ i ∈ Finset.range (NN + 1), krT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ≤ ((epData (mkCtx iLoNum 128) kc Xc).kr : ℝ) ∧
    (epData (mkCtx iLoNum 128) kc Xc).cl = ∑ i ∈ Finset.range (NN + 1), clT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ∧
    (epData (mkCtx iLoNum 128) kc Xc).cle = ∑ i ∈ Finset.range (NN + 1), cleT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ∧
    (((epData (mkCtx iLoNum 128) kc Xc).apl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ∧
      2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ≤ ((epData (mkCtx iLoNum 128) kc Xc).aph : ℝ)) ∧
    (((epData (mkCtx iLoNum 128) kc Xc).anl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ∧
      2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((Xc : ℝ) / ((DEC * 2 ^ kc : ℕ) : ℝ)) i ≤ ((epData (mkCtx iLoNum 128) kc Xc).anh : ℝ)) := by
  have hLDs := logT_D kc
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := epPass_range (k := kc) (X := Xc) hLDs (NN + 1) le_rfl
  have hs : (((List.range (NN + 1)).map recOf).foldl
      (epStep TAB L2 kc Xc ((DEC * 2 ^ kc * (DEC * 2 ^ kc) : ℕ) : ℤ) (logT TAB L2 (DEC * 2 ^ kc) 1)) epZero).s =
      pointPass TAB L2 mkRecs kc Xc (logT TAB L2 (DEC * 2 ^ kc) 1) := by
    rw [epPass_s, mkRecs_eq]; rfl
  have hU := pointPass_sound (k := kc) (X := Xc) hLDs
  simp only at hU
  have hu := uHi_sound (k := kc) (X := Xc) (S := pointPass TAB L2 mkRecs kc Xc (logT TAB L2 (DEC * 2 ^ kc) 1)) hU.2
  rw [epData_eq, hs]
  dsimp only
  exact ⟨hu, h2, h3, h4, h5, h6, h7, h8⟩

/-- **The end-point data** at `x = X / (10^12 2^k)` (computed at the reduced scale). -/
theorem epAt_spec (X k : ℕ) :
    2 ^ P * UR ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) ≤ ((epAt (mkCtx iLoNum 128) X k).uhi : ℝ) ∧
    ((epAt (mkCtx iLoNum 128) X k).g0 : ℝ) ≤ 2 ^ (P + QS) * ∑ i ∈ Finset.range (NN + 1), gT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
    2 ^ QS * ∑ i ∈ Finset.range (NN + 1), klT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ ((epAt (mkCtx iLoNum 128) X k).kl : ℝ) ∧
    2 ^ QS * ∑ i ∈ Finset.range (NN + 1), krT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ ((epAt (mkCtx iLoNum 128) X k).kr : ℝ) ∧
    (epAt (mkCtx iLoNum 128) X k).cl = ∑ i ∈ Finset.range (NN + 1), clT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
    (epAt (mkCtx iLoNum 128) X k).cle = ∑ i ∈ Finset.range (NN + 1), cleT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
    (((epAt (mkCtx iLoNum 128) X k).apl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      2 ^ QS * ∑ i ∈ Finset.range (NN + 1), apT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ ((epAt (mkCtx iLoNum 128) X k).aph : ℝ)) ∧
    (((epAt (mkCtx iLoNum 128) X k).anl : ℝ) ≤ 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ∧
      2 ^ QS * ∑ i ∈ Finset.range (NN + 1), anT ((X : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)) i ≤ ((epAt (mkCtx iLoNum 128) X k).anh : ℝ)) := by
  have h := epData_spec (canon X k).2 (canon X k).1
  rw [canon_real X k] at h
  exact h

end Trace86.Cert
