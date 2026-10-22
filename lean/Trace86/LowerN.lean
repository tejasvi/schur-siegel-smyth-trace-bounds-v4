import Trace86.LeavesN
import Trace86.TailSound2
import Trace86.EnergySound
import Trace86.CertData
import T86N.Globals
import AuxCommon.EnergyProof

/-!
# The 86a lower bound, native track (N)

The certificate checks are the `native_decide` shards of `T86N` (`Globals`: data, energy, tails; `ChunkNNN`: the
tiling of `[1/100, 30)` in end-point form, `leavesOKE`), composed with the soundness theorems of the checker. `EnergySmoothing` is discharged by
`AuxCommon.energySmoothing` (AuxCommon/EnergyProof.lean, a shared module), so the theorems have no
hypotheses.

* `IR_ge_N`: `I(ρ) ≥ iLoNum / 2^128`;
* `FR_pos_N`: `F(x) > 0` for `x > 0` off the roots of the `Qⱼ` (left tail, leaves, right tail);
* `certHyp_N`: the certificate as `CertHyp Qc cR lamR NN eR GR sR`;
* `trace_lower_N`, `trace_lower_dec_N`: the lower bound `C₈₆ ≥ λ_L` and its decimal form.
-/

open Set

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

theorem IR_ge_N : (iLoNum : ℝ) / 2 ^ 128 ≤ IR := energy_sound (of_decide_eq_true T86Core.T86N.energy_ok)

theorem FR_pos_N (x : ℝ) (hx : 0 < x) (hQx : ∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) : 0 < FR x := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hD0 : ((DEC * 2 ^ 0 : ℕ) : ℝ) = (DEC : ℝ) := by push_cast; ring
  rcases le_or_gt x ((10000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) with h1 | h1
  · -- the left tail `(0, 1/100]`
    have hl := T86Core.T86N.left_tail_ok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨hpre, hpos⟩ := hl
    have h := leftTailLB_sound IR_ge_N hpre hx h1 hQx
    have : (0 : ℝ) < (leftTailLB (mkCtx iLoNum 128) 10000000000 0 : ℝ) / 2 ^ P :=
      div_pos (by exact_mod_cast hpos) hP
    linarith
  · rcases lt_or_ge x ((30000000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) with h2 | h2
    · -- the leaves `[1/100, 30)` (the first leaf starts at `80000000000 / (10^12 2^3) = 1/100`)
      have hX0 : ((80000000000 : ℕ) / (DEC * 2 ^ 3 : ℕ) : ℝ) = ((10000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) := by
        norm_num [DEC]
      exact FR_pos_leaves_N IR_ge_N x ⟨by rw [hX0]; exact h1.le, h2⟩ hQx
    · -- the right tail `[30, ∞)`
      have hr := T86Core.T86N.right_tail_ok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨hpre, hpos⟩ := hr
      rw [hD0] at h2
      have h := rightTailLB_sound IR_ge_N hpre h2 hQx
      have : (0 : ℝ) < (rightTailLB (mkCtx iLoNum 128) 30000000000000 : ℝ) / 2 ^ P :=
        div_pos (by exact_mod_cast hpos) hP
      linarith

/-- **The certificate (N).** -/
theorem certHyp_N : CertHyp Qc cR lamR NN eR GR sR :=
  certHyp_of (fun x hx hQx => (FR_pos_N x hx hQx).le)

theorem lamR_eq : lamR = lamL := by
  unfold lamR lamL
  norm_num [lamNum, lamDen]

end Trace86.Cert

namespace Trace86

open AuxCommon

theorem TPTraceLe_mono {B B' : ℝ} (h : B ≤ B') : TPTraceLe B ⊆ TPTraceLe B' := by
  rintro α ⟨hint, P, hP, hpos, hle⟩
  exact ⟨hint, P, hP, hpos, hle.trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))⟩

/-- **Lower bound (N).** For every `ε > 0`, only finitely many totally positive algebraic integers satisfy
`tr(α) ≤ (λ_L - ε) deg(α)`; that is, `C₈₆ ≥ λ_L`. (The reviewed statement, with its
hypothesis `EnergySmoothing` discharged by `AuxCommon.energySmoothing`.) -/
theorem trace_lower_N (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamL - ε)).Finite := by
  have h := Cert.certHyp_N.trace_main energySmoothing ε hε
  rwa [Cert.lamR_eq] at h

/-- The decimal form (N): all but finitely many totally positive algebraic integers satisfy
`tr(α) > 1.8022225 deg(α)`. -/
theorem trace_lower_dec_N : (TPTraceLe (18022225 / 10000000)).Finite := by
  have hlt : (18022225 / 10000000 : ℝ) < lamL := by
    unfold lamL
    norm_num
  have h := trace_lower_N (lamL - 18022225 / 10000000) (by linarith)
  rwa [sub_sub_cancel] at h

end Trace86
