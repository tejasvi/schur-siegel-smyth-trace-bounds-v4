import Trace86.EnergySound
import T86K.ELits

/-!
# Assembling the energy from kernel-checked chunks (K)

Adapted from the companion formalizations' energy-chunk lemmas.

The kernel's cost of one `decide +kernel` grows faster than linearly in the work it does, so the K track checks the
energy `(iBlock 0 10388).1` in chunks: one row of `iBlockAux` restricted to at most 200 columns per theorem
(`T86K/EchkNNNN.lean`, over the literal inputs of `T86K/ELits.lean`). This file has the exact additivity lemmas:
`iRow` over a concatenation, and the recursion `blkK i = (row i) + blkK (i + 1)` of the row sums.
-/

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

theorem iRowStep_fst (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (ri : NRec) (acc : ℤ × ℤ) (rk : NRec) :
    (iRowStep tab l2 lDec ri acc rk).1 = acc.1 + (iRowStep tab l2 lDec ri (0, 0) rk).1 := by
  unfold iRowStep
  split_ifs <;> simp

theorem foldl_iRowStep_fst (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (ri : NRec) :
    ∀ (l : List NRec) (acc : ℤ × ℤ),
      (l.foldl (iRowStep tab l2 lDec ri) acc).1 = acc.1 + (l.foldl (iRowStep tab l2 lDec ri) (0, 0)).1
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, List.foldl_cons, foldl_iRowStep_fst tab l2 lDec ri xs (iRowStep tab l2 lDec ri acc x),
      foldl_iRowStep_fst tab l2 lDec ri xs (iRowStep tab l2 lDec ri (0, 0) x), iRowStep_fst]
    ring

theorem iRow_fst_append (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (ri : NRec) (l1 l2' : List NRec) :
    (iRow tab l2 lDec ri (l1 ++ l2')).1 = (iRow tab l2 lDec ri l1).1 + (iRow tab l2 lDec ri l2').1 := by
  rw [iRow_eq, iRow_eq, iRow_eq, List.foldl_append, foldl_iRowStep_fst]

theorem iBlockAux_fst_acc (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) :
    ∀ (cnt : ℕ) (rs : List NRec) (acc : ℤ × ℤ),
      (iBlockAux tab l2 lDec cnt rs acc).1 = acc.1 + (iBlockAux tab l2 lDec cnt rs (0, 0)).1
  | 0, rs, acc => by simp [iBlockAux]
  | c + 1, [], acc => by simp [iBlockAux]
  | c + 1, r :: rest, acc => by
    simp only [iBlockAux]
    conv_lhs => rw [iBlockAux_fst_acc tab l2 lDec c rest]
    conv_rhs => rw [iBlockAux_fst_acc tab l2 lDec c rest]
    simp only [zero_add]
    ring

theorem iBlockAux_fst_cons (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (c : ℕ) (r : NRec) (rest : List NRec) :
    (iBlockAux tab l2 lDec (c + 1) (r :: rest) (0, 0)).1 =
      (if r.sg = 0 then 0 else (iRow tab l2 lDec r rest).1) + (iBlockAux tab l2 lDec c rest (0, 0)).1 := by
  simp only [iBlockAux]
  rw [iBlockAux_fst_acc]
  split_ifs <;> simp

theorem recsILit_length : recsILit.length = 10388 := by decide +kernel

/-- `(l.drop a).take n ++ l.drop b = l.drop a` when `a + n = b`. -/
theorem take_append_drop_eq (l : List NRec) (a n b : ℕ) (h : a + n = b) :
    (l.drop a).take n ++ l.drop b = l.drop a := by
  subst h
  have h := List.take_append_drop n (l.drop a)
  rwa [List.drop_drop] at h

/-- The row sums of the literal energy, from row `i` on. -/
def blkK (i : ℕ) : ℤ := (iBlockAux tabILit l2ILit lDecL (10388 - i) (recsILit.drop i) (0, 0)).1

/-- Row `i` of the literal energy. -/
def rowK (i : ℕ) : ℤ := (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) (recsILit.drop (i + 1))).1

theorem blkK_step (i j : ℕ) (hij : i + 1 = j) (hi : i < 10388) :
    blkK i = (if (recsILit.getD i dfl).sg = 0 then 0 else rowK i) + blkK j := by
  subst hij
  unfold blkK rowK
  have h1 : 10388 - i = (10388 - (i + 1)) + 1 := by omega
  have hl : i < recsILit.length := by rw [recsILit_length]; exact hi
  have h2 : recsILit.drop i = recsILit.getD i dfl :: recsILit.drop (i + 1) := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.drop_eq_getElem_cons hl
  rw [h1, h2, iBlockAux_fst_cons]

theorem blkK_end : blkK 10388 = 0 := by
  unfold blkK
  rw [Nat.sub_self]
  rfl

theorem rowK_of_chunks_last (i a m : ℕ) (ha : a + m = 10388) {v : ℤ}
    (h : (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) ((recsILit.drop a).take m)).1 = v) :
    (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) (recsILit.drop a)).1 = v := by
  rwa [List.take_of_length_le (by rw [List.length_drop, recsILit_length]; omega)] at h

theorem rowK_of_chunks_step (i a m b : ℕ) (hab : a + m = b) {v w s : ℤ}
    (h1 : (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) ((recsILit.drop a).take m)).1 = v)
    (h2 : (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) (recsILit.drop b)).1 = w) (hs : v + w = s) :
    (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) (recsILit.drop a)).1 = s := by
  rw [← take_append_drop_eq recsILit a m b hab, iRow_fst_append, h1, h2, hs]

theorem rowK_eq (i : ℕ) {v : ℤ}
    (h : (iRow tabILit l2ILit lDecL (recsILit.getD i dfl) (recsILit.drop (i + 1))).1 = v) : rowK i = v := h

theorem blkK_step_zero (i j : ℕ) (hij : i + 1 = j) (hi : i < 10388) (hz : (recsILit.getD i dfl).sg = 0) :
    blkK i = blkK j := by
  rw [blkK_step i j hij hi, if_pos hz, zero_add]

theorem blkK_step_row (i j : ℕ) (hij : i + 1 = j) (hi : i < 10388) (hz : (recsILit.getD i dfl).sg ≠ 0) {v : ℤ}
    (hr : rowK i = v) : blkK i = v + blkK j := by
  rw [blkK_step i j hij hi, if_neg hz, hr]

end Trace86.Cert
