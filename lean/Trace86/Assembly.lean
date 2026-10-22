import Trace86.Reduction
import Trace86.Measure
import Trace86.ClosedForm

/-!
# Assembly of the lower bound from the certificate inequality (trace version of the companion Mahler-measure formalization's assembly)

`CertHyp Q c m N e G s` collects the data conditions and the certificate inequality in closed form:
`F(x) = x - m - ∑ cⱼ log |Qⱼ(x)| - 2 ∑ᵢ Cᵢ H(eᵢ - x) + (∑ᵢₖ Cᵢ Cₖ L(eᵢ - eₖ)) / s ≥ 0` for `x > 0` off the roots.
From it, with `ν = ρ / s` (`nuPw`), `λ = s`, `K = 2 ∑ₖ Gₖ / s`, the closed forms (`pwLinClosedForm`, proved) and the
named hypothesis `EnergySmoothing` (the only one): `CertHyp.trace_main`, `TPTraceLe (m - ε)` is finite for every
`ε > 0`. (No degree budget: algebraic integers have leading coefficient `±1`.)
-/

open Polynomial MeasureTheory Filter Topology
open AuxCommon

namespace Trace86

/-- The data conditions and the certificate inequality of the 86a lower bound (closed form of `F`, `λ = s`). -/
structure CertHyp {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (m : ℝ) (N : ℕ) (e G : ℕ → ℝ) (s : ℝ) :
    Prop where
  Q_ne_zero : ∀ j, Q j ≠ 0
  c_nonneg : ∀ j, 0 ≤ c j
  nodes : ∀ k < N, e k < e (k + 1)
  G_nonneg : ∀ k ≤ N, 0 ≤ G k
  G_first : G 0 = 0
  G_last : G N = 0
  mass : ∑ k ∈ Finset.range N, (e (k + 1) - e k) * (G k + G (k + 1)) / 2 = s
  mass_pos : 0 < s
  F_nonneg : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
    0 ≤ x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
      2 * ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x) +
      (∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        slopeJump N e G i * slopeJump N e G k * Lk (e i - e k)) / s

namespace CertHyp

variable {J : ℕ} {Q : Fin J → ℤ[X]} {c : Fin J → ℝ} {m : ℝ} {N : ℕ} {e G : ℕ → ℝ} {s : ℝ}

/-- An upper bound for the node values: their sum. -/
theorem G_le_sum (h : CertHyp Q c m N e G s) {k : ℕ} (hk : k ≤ N) :
    G k ≤ ∑ i ∈ Finset.range (N + 1), G i :=
  Finset.single_le_sum (f := G) (fun i hi => h.G_nonneg i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem sum_G_pos (h : CertHyp Q c m N e G s) : 0 < ∑ i ∈ Finset.range (N + 1), G i := by
  by_contra hle
  push Not at hle
  have hG0 : ∀ k ≤ N, G k = 0 := fun k hk =>
    le_antisymm ((h.G_le_sum hk).trans hle) (h.G_nonneg k hk)
  have hs0 : s = 0 := by
    rw [← h.mass]
    apply Finset.sum_eq_zero
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [hG0 k hk.le, hG0 (k + 1) hk]
    ring
  exact h.mass_pos.ne' hs0

/-- The constant of the disc bound, `K = 2 ∑ₖ Gₖ / s`. -/
noncomputable def Kc (_h : CertHyp Q c m N e G s) : ℝ := 2 * (∑ i ∈ Finset.range (N + 1), G i) / s

theorem Kc_pos (h : CertHyp Q c m N e G s) : 0 < h.Kc := by
  unfold Kc
  have := h.sum_G_pos
  have := h.mass_pos
  positivity

theorem isProbabilityMeasure (h : CertHyp Q c m N e G s) : IsProbabilityMeasure (nuPw N e G s) :=
  isProbabilityMeasure_nuPw h.nodes h.G_nonneg h.mass h.mass_pos

theorem compactSupp (h : CertHyp Q c m N e G s) : CompactSupp (nuPw N e G s) :=
  compactSupp_nuPw h.nodes s

theorem discBound (h : CertHyp Q c m N e G s) : DiscBound (nuPw N e G s) h.Kc :=
  discBound_nuPw h.nodes h.G_nonneg (fun _ hk => h.G_le_sum hk) h.mass_pos

/-- The auxiliary inequality of Lemma T1 for `ν = ρ / s` and `λ = s`, from the closed form. -/
theorem auxIneq (h : CertHyp Q c m N e G s) :
    ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        s * (2 * logPot (nuPw N e G s) x - logEnergy (nuPw N e G s)) := by
  intro x hx hQx
  rw [logPot_nuPw_eq_closedForm pwLinClosedForm h.nodes h.G_nonneg h.G_first h.G_last h.mass_pos,
    logEnergy_nuPw_eq_closedForm pwLinClosedForm h.nodes h.G_nonneg h.G_first h.G_last h.mass_pos]
  have hF := h.F_nonneg x hx hQx
  have hs := h.mass_pos
  set A := ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x)
  set B := ∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    slopeJump N e G i * slopeJump N e G k * Lk (e i - e k)
  have key : s * (2 * (1 / s * A) - 1 / s ^ 2 * B) = 2 * A - B / s := by
    field_simp
  rw [key]
  linarith

/-- **The lower bound** from the certificate inequality: `TPTraceLe (m - ε)` is finite for every `ε > 0`. -/
theorem trace_main (h : CertHyp Q c m N e G s) (hE : EnergySmoothing) (ε : ℝ)
    (hε : 0 < ε) : (TPTraceLe (m - ε)).Finite :=
  haveI := h.isProbabilityMeasure
  cor_trace hE Q c s m h.Kc (nuPw N e G s) h.Q_ne_zero h.c_nonneg h.mass_pos.le h.Kc_pos h.compactSupp
    h.discBound h.auxIneq ε hε

end CertHyp

end Trace86
