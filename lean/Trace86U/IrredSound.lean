import Trace86U.MomentSound
import Trace86U.CertData

/-!
# Irreducibility of the upper certificate polynomials (for Lemma U1, step 2)

`irreducible_of_brackets`: a monic `Qd q` whose roots are all real, one in each of `deg` disjoint brackets
(`momentOK`), is irreducible in `ℤ[X]` if no proper nonempty set of brackets admits an integer root sum (`irredOK`): a
monic factor `f` of degree `0 < m < deg` has its roots among those of `Qd q` and the integer `-nextCoeff f` as their
sum.
-/

open Polynomial Set

namespace Trace86.UCert

open T86UCore

theorem mem_subl_of_sublist {α : Type} : ∀ {t l : List α}, t.Sublist l → t ∈ subl l
  | _, [], h => by rw [List.sublist_nil.mp h]; simp [subl]
  | t, a :: l, h => by
    simp only [subl, List.mem_append, List.mem_map]
    cases h with
    | cons _ h' => exact Or.inl (mem_subl_of_sublist h')
    | cons_cons _ h' => exact Or.inr ⟨_, mem_subl_of_sublist h', rfl⟩

theorem noIntIn_spec {lo hi D : ℕ} (hD : 0 < D) (h : noIntIn lo hi D = true) (n : ℕ) :
    ¬ (lo ≤ n * D ∧ n * D ≤ hi) := by
  rintro ⟨h1, h2⟩
  unfold noIntIn at h
  simp only [decide_eq_true_eq] at h
  have hn1 : n ≤ hi / D := (Nat.le_div_iff_mul_le hD).mpr h2
  have hn2 : (lo + D - 1) / D < n + 1 := by
    rw [Nat.div_lt_iff_lt_mul hD, Nat.add_mul, one_mul]
    omega
  omega

theorem sum_div_eq (t : List (ℕ × ℕ)) (f : ℕ × ℕ → ℕ) (D : ℝ) :
    ((t.map f).sum : ℝ) / D = (t.map (fun b => (f b : ℝ) / D)).sum := by
  induction t with
  | nil => simp
  | cons b t ih => rw [List.map_cons, List.sum_cons, Nat.cast_add, add_div, ih, List.map_cons, List.sum_cons]

theorem foldl_fst_sum (t : List (ℕ × ℕ)) :
    t.foldl (fun a b => a + b.1) 0 = (t.map Prod.fst).sum := by
  have h := foldl_add_eq_sum (fun b : ℕ × ℕ => b.1) t 0
  rw [zero_add] at h
  exact h

theorem foldl_snd_sum (t : List (ℕ × ℕ)) :
    t.foldl (fun a b => a + b.2) 0 = (t.map Prod.snd).sum := by
  have h := foldl_add_eq_sum (fun b : ℕ × ℕ => b.2) t 0
  rw [zero_add] at h
  exact h

/-- **Irreducibility from the brackets.** -/
theorem irreducible_of_brackets {q : List ℤ} {k : ℕ} {bs : List (ℕ × ℕ)} (hm : momentOK mkCtx q k bs = true)
    (hi : irredOK k bs = true) (hmon : (Qd q).Monic) (hdeg : (Qd q).natDegree = q.length - 1)
    (hpos : 0 < q.length - 1) : Irreducible (Qd q) := by
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hinj : Function.Injective (Int.castRingHom ℝ) := RingHom.injective_int _
  have hq0 : Qd q ≠ 0 := hmon.ne_zero
  have hq0R : QR q ≠ 0 := by
    unfold QR
    exact (Polynomial.map_ne_zero_iff hinj).mpr hq0
  have hdegR : (QR q).natDegree = q.length - 1 := by
    unfold QR
    rw [natDegree_map_eq_of_injective hinj, hdeg]
  obtain ⟨hroots, hr06, -⟩ := moment_one hm hq0R hdegR
  have hm' := hm
  unfold momentOK at hm'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hm'
  obtain ⟨⟨⟨⟨hlen, hord⟩, hok⟩, -⟩, -⟩ := hm'
  set D : ℕ := DEC * 2 ^ k with hDdef
  set rs : List ℝ := bs.map (rootOf q D) with hrs
  have hnd : rs.Nodup :=
    (roots_pairwise hD hok (bracketsOrdered_pairwise bs hord (fun b hb => bracket_le (hok b hb)))).imp
      (fun h => ne_of_lt h)
  have hsplit : (QR q).Splits := by
    rw [splits_iff_card_roots, hroots, Multiset.coe_card, hrs, List.length_map, hlen, hdegR]
  rw [hmon.irreducible_iff_natDegree]
  refine ⟨?_, fun f g hf hg hfg => ?_⟩
  · intro h
    rw [h, natDegree_one] at hdeg
    omega
  · by_contra hcon
    push Not at hcon
    obtain ⟨hf0, hg0⟩ := hcon
    have hdsum : f.natDegree + g.natDegree = q.length - 1 := by
      rw [← hdeg, ← hfg, hf.natDegree_mul hg]
    set fR := f.map (Int.castRingHom ℝ) with hfR
    have hdvd : fR ∣ QR q := ⟨g.map (Int.castRingHom ℝ), by rw [hfR, ← Polynomial.map_mul, hfg]; rfl⟩
    have hfsplit : fR.Splits := hsplit.of_dvd hq0R hdvd
    have hfmon : fR.Monic := hf.map _
    have hle : fR.roots ≤ (QR q).roots := roots.le_of_dvd hq0R hdvd
    have hfdeg : fR.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
    -- the roots of `fR` are the roots of a sublist `t` of the brackets
    set t := bs.filter (fun b => decide (rootOf q D b ∈ fR.roots)) with ht
    have hfroots : fR.roots = ((t.map (rootOf q D) : List ℝ) : Multiset ℝ) := by
      have hndf : fR.roots.Nodup := Multiset.nodup_of_le hle (by rw [hroots]; exact Multiset.coe_nodup.mpr hnd)
      have hndt : (t.map (rootOf q D)).Nodup := by
        have : (t.map (rootOf q D)).Sublist rs := List.filter_sublist.map _
        exact this.nodup hnd
      rw [Multiset.Nodup.ext hndf (Multiset.coe_nodup.mpr hndt)]
      intro x
      rw [Multiset.mem_coe, List.mem_map]
      constructor
      · intro hx
        have hx' : x ∈ (QR q).roots := Multiset.mem_of_le hle hx
        rw [hroots, Multiset.mem_coe, hrs, List.mem_map] at hx'
        obtain ⟨b, hb, rfl⟩ := hx'
        exact ⟨b, List.mem_filter.mpr ⟨hb, by simpa using hx⟩, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        simpa using (List.mem_filter.mp hb).2
    have htlen : t.length = f.natDegree := by
      have h1 := hfsplit.natDegree_eq_card_roots
      rw [hfroots, Multiset.coe_card, List.length_map] at h1
      rw [← h1, hfdeg]
    -- the root sum is an integer
    have hsum : (t.map (rootOf q D)).sum = -(f.nextCoeff : ℝ) := by
      have h1 := hfsplit.nextCoeff_eq_neg_sum_roots_of_monic hfmon
      rw [hfR, nextCoeff_map hinj, hfroots, Multiset.sum_coe] at h1
      simp only [eq_intCast] at h1
      linarith
    -- the root sum is in the bracket sums
    have hrt : ∀ b ∈ t, (b.1 : ℝ) / D ≤ rootOf q D b ∧ rootOf q D b ≤ (b.2 : ℝ) / D := by
      intro b hb
      obtain ⟨h1, h2, -⟩ := rootOf_spec hD (hok b (List.mem_of_mem_filter hb))
      exact ⟨h1, h2⟩
    have hlo : ((t.map Prod.fst).sum : ℝ) / D ≤ (t.map (rootOf q D)).sum := by
      rw [sum_div_eq]
      apply List.sum_le_sum
      intro b hb
      exact (hrt b hb).1
    have hhi : (t.map (rootOf q D)).sum ≤ ((t.map Prod.snd).sum : ℝ) / D := by
      rw [sum_div_eq]
      apply List.sum_le_sum
      intro b hb
      exact (hrt b hb).2
    -- irredOK at `t`
    have hit := List.all_eq_true.mp hi t (mem_subl_of_sublist List.filter_sublist)
    simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq] at hit
    have htne : t ≠ [] := by
      intro h0
      rw [h0, List.length_nil] at htlen
      exact hf0 htlen.symm
    have htfull : t.length ≠ bs.length := by
      rw [htlen, hlen]
      omega
    rcases hit with (h0 | h0) | hno
    · exact htne h0
    · exact htfull h0
    · rw [foldl_fst_sum, foldl_snd_sum] at hno
      -- the integer root sum `n = -nextCoeff f ≥ 0`
      have hnn : (0 : ℝ) ≤ (t.map (rootOf q D)).sum := by
        apply List.sum_nonneg
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨b, hb, rfl⟩ := hx
        have : rootOf q D b ∈ rs := by
          rw [hrs, List.mem_map]
          exact ⟨b, List.mem_of_mem_filter hb, rfl⟩
        exact (hr06 _ this).1
      rw [hsum] at hlo hhi hnn
      have hn0 : 0 ≤ -f.nextCoeff := by exact_mod_cast hnn
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hn0
      have hnR : -(f.nextCoeff : ℝ) = (n : ℝ) := by exact_mod_cast hn
      rw [hnR] at hlo hhi
      apply noIntIn_spec hD hno n
      constructor
      · have := (div_le_iff₀ hDR).mp hlo
        exact_mod_cast this
      · have := (le_div_iff₀ hDR).mp hhi
        exact_mod_cast this

end Trace86.UCert
