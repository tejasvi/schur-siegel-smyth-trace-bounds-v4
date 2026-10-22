import Trace86U.TailSound2

/-!
# The first moment of the upper density (condition (T))

`∫ y G(y) dy = (1/6) ∑ᵢ Cᵢ eᵢ³` (generic closed form with `Φ = t³/6`), and summation by parts regroups this by hats:
`∑ᵢ Cᵢ eᵢ³ = 2 ∑ₖ wₖ (e_{k-1} + e_k + e_{k+1})`, which is `2 traceNum / (WD 10^12)` (`traceNum` of the checker).
-/

open Polynomial Set MeasureTheory

namespace Trace86.UCert

open T86UCore

theorem integral_mul_id_pwLin :
    ∫ y, y * pwLin NN eR GR y = (∑ i ∈ Finset.range (NN + 1), slopeJump NN eR GR i * eR i ^ 3) / 6 := by
  have hΦ : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun x : ℝ => x ^ 3 / 6) ((fun x : ℝ => x ^ 2 / 2) t) t := by
    intro t _
    have := (hasDerivAt_pow 3 t).div_const 6
    convert this using 1
    push_cast
    ring
  have hφ : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun x : ℝ => x ^ 2 / 2) ((fun x : ℝ => x) t) t := by
    intro t _
    have := (hasDerivAt_pow 2 t).div_const 2
    convert this using 1
    push_cast
    ring
  have h := integral_mul_pwLin (Φ := fun x : ℝ => x ^ 3 / 6) (φ := fun x : ℝ => x ^ 2 / 2) (ψ := fun x : ℝ => x)
    (by fun_prop) (by fun_prop) hΦ hφ 0 (fun a b => (continuous_id.sub continuous_const).intervalIntegrable a b)
    eR_lt GR_zero GR_NN
  simp only [sub_zero] at h
  rw [h, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem sum_slopeJump_cube :
    ∑ i ∈ Finset.range (NN + 1), slopeJump NN eR GR i * eR i ^ 3 =
      ∑ k ∈ Finset.range (NN + 1),
        (if 0 < k ∧ k < NN then 2 * rhoR k * (eR (k - 1) + eR k + eR (k + 1)) else 0) := by
  rw [sum_slopeJump_mul]
  set S : ℕ → ℝ := fun k => eR (k + 1) ^ 2 + eR (k + 1) * eR k + eR k ^ 2 with hSdef
  have hS : ∀ k ∈ Finset.range NN, slope eR GR k * (eR (k + 1) ^ 3 - eR k ^ 3) =
      GR (k + 1) * S k - GR k * S k := by
    intro k hk
    have h := eR_lt k (Finset.mem_range.mp hk)
    unfold slope
    have hne : eR (k + 1) - eR k ≠ 0 := by linarith
    simp only [hSdef]
    field_simp
    ring
  rw [Finset.sum_congr rfl hS, Finset.sum_sub_distrib]
  have h2 : ∑ k ∈ Finset.range NN, GR (k + 1) * S k =
      ∑ j ∈ Finset.range (NN + 1), (if 0 < j then GR j * S (j - 1) else 0) := by
    rw [Finset.sum_range_succ' (fun j => if 0 < j then GR j * S (j - 1) else 0)]
    simp
  have h1 : ∑ k ∈ Finset.range NN, GR k * S k = ∑ k ∈ Finset.range (NN + 1), GR k * S k := by
    rw [Finset.sum_range_succ, GR_NN]
    simp
  rw [h2, h1, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  by_cases hint : 0 < k ∧ k < NN
  · obtain ⟨hk0, hkN⟩ := hint
    rw [if_pos hk0, if_pos ⟨hk0, hkN⟩]
    unfold GR
    rw [if_pos ⟨hk0, hkN⟩]
    have h1 := eR_lt (k - 1) (by omega)
    have h2 := eR_lt k hkN
    rw [show k - 1 + 1 = k by omega] at h1
    have hpos : eR (k + 1) - eR (k - 1) ≠ 0 := by linarith
    simp only [hSdef]
    rw [show k - 1 + 1 = k by omega]
    field_simp
    ring
  · have hG : GR k = 0 := by unfold GR; rw [if_neg hint]
    rw [hG, if_neg hint]
    split_ifs <;> simp

theorem foldl_trace_eq : ∀ (r n : List ℕ) (acc : ℕ), r.length + 2 ≤ n.length →
    (List.zip r (List.zip n (List.zip (n.drop 1) (n.drop 2)))).foldl
      (fun acc t => acc + t.1 * (t.2.1 + t.2.2.1 + t.2.2.2)) acc =
    acc + ∑ i ∈ Finset.range r.length, r.getD i 0 * (n.getD i 0 + n.getD (i + 1) 0 + n.getD (i + 2) 0)
  | [], n, acc, _ => by simp
  | _ :: _, [], _, h => by simp at h
  | _ :: _, [_], _, h => by simp at h
  | _ :: _, [_, _], _, h => by simp at h
  | r0 :: r', n0 :: n1 :: n2 :: rest, acc, h => by
    have hlen : r'.length + 2 ≤ (n1 :: n2 :: rest).length := by simp at h ⊢; omega
    have e1 : (n0 :: n1 :: n2 :: rest).drop 1 = n1 :: n2 :: rest := rfl
    have e2 : (n0 :: n1 :: n2 :: rest).drop 2 = n2 :: rest := rfl
    have e3 : (n1 :: n2 :: rest).drop 1 = n2 :: rest := rfl
    have e4 : (n1 :: n2 :: rest).drop 2 = rest := rfl
    rw [e1, e2]
    simp only [List.zip_cons_cons, List.foldl_cons]
    have ih := foldl_trace_eq r' (n1 :: n2 :: rest) (acc + r0 * (n0 + n1 + n2)) hlen
    rw [e3, e4] at ih
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem rho_len_le : rho.length + 2 ≤ nodes.length := by
  have h1 := rho_length
  have h2 := nodes_length
  omega

theorem traceNum_eq_foldl : traceNum = (List.zip rho (List.zip nodes (List.zip (nodes.drop 1) (nodes.drop 2)))).foldl
      (fun acc t => acc + t.1 * (t.2.1 + t.2.2.1 + t.2.2.2)) 0 := by
  unfold traceNum
  rfl

theorem traceNum_eq_sum : traceNum = ∑ i ∈ Finset.range rho.length,
    rho.getD i 0 * (nodes.getD i 0 + nodes.getD (i + 1) 0 + nodes.getD (i + 2) 0) :=
  traceNum_eq_foldl.trans ((foldl_trace_eq rho nodes 0 rho_len_le).trans (Nat.zero_add _))

/-- `traceNum / (WD 10^12) = ∑ₖ wₖ (e_{k-1} + e_k + e_{k+1})`. -/
theorem traceNum_eq : ((traceNum : ℕ) : ℝ) / ((WD : ℝ) * 10 ^ 12) =
    ∑ k ∈ Finset.range (NN + 1), (if 0 < k ∧ k < NN then rhoR k * (eR (k - 1) + eR k + eR (k + 1)) else 0) := by
  rw [traceNum_eq_sum]
  have hlen : rho.length = NN - 1 := by have := rho_length; omega
  rw [hlen, Nat.cast_sum, Finset.sum_div]
  rw [Finset.sum_range_succ' (fun k => if 0 < k ∧ k < NN then rhoR k * (eR (k - 1) + eR k + eR (k + 1)) else 0)]
  rw [if_neg (by omega), add_zero]
  have hNN1 : NN - 1 + 1 = NN := by unfold NN; norm_num
  rw [← hNN1, Finset.sum_range_succ, if_neg (by omega), add_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < NN - 1 := Finset.mem_range.mp hi
  rw [if_pos ⟨Nat.succ_pos i, by omega⟩]
  have hWD : (0 : ℝ) < WD := by unfold WD; norm_num
  have e1 : rhoR (i + 1) = (rho.getD i 0 : ℝ) / WD := by unfold rhoR; rw [Nat.add_sub_cancel]
  have e2 : eR (i + 1 - 1) = (nodes.getD i 0 : ℝ) / 10 ^ 12 := by unfold eR; rw [Nat.add_sub_cancel]
  have e3 : eR (i + 1) = (nodes.getD (i + 1) 0 : ℝ) / 10 ^ 12 := rfl
  have e4 : eR (i + 1 + 1) = (nodes.getD (i + 2) 0 : ℝ) / 10 ^ 12 := rfl
  rw [e1, e2, e3, e4]
  push_cast
  generalize (rho.getD i 0 : ℝ) = a
  generalize (nodes.getD i 0 : ℝ) = b
  generalize (nodes.getD (i + 1) 0 : ℝ) = c
  generalize (nodes.getD (i + 2) 0 : ℝ) = d
  generalize (WD : ℝ) = W at hWD ⊢
  field_simp

/-- **The first moment.** `∫ y G(y) dy = traceNum / (3 WD 10^12)`. -/
theorem integral_mul_id_pwLin_eq :
    ∫ y, y * pwLin NN eR GR y = ((traceNum : ℕ) : ℝ) / (3 * ((WD : ℝ) * 10 ^ 12)) := by
  rw [integral_mul_id_pwLin, sum_slopeJump_cube]
  have h := traceNum_eq
  have hWD : (0 : ℝ) < WD := by unfold WD; norm_num
  have e : ∑ k ∈ Finset.range (NN + 1),
      (if 0 < k ∧ k < NN then 2 * rhoR k * (eR (k - 1) + eR k + eR (k + 1)) else 0) =
      2 * ∑ k ∈ Finset.range (NN + 1),
        (if 0 < k ∧ k < NN then rhoR k * (eR (k - 1) + eR k + eR (k + 1)) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> ring
  rw [e, ← h]
  generalize ((traceNum : ℕ) : ℝ) = T
  generalize (WD : ℝ) = W at hWD ⊢
  field_simp
  ring

end Trace86.UCert
