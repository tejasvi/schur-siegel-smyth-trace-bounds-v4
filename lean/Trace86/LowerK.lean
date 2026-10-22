import Trace86.LeavesK
import Trace86.EnergyK
import Trace86.TailSound2
import Trace86.CertData
import T86K.Globals
import T86K.Lits
import AuxCommon.EnergyProof

/-!
# The 86a lower bound, kernel-only track (K)

The certificate checks are `decide +kernel` shards: `T86K.Globals` (data, left and right tail over the literal context
`ctxLit`), `T86K.Lits` (`mkCtx iLoNum 128 = ctxLit`), `T86KE.EpNNNNN` (the end-point data of the tiling, one point
each) and `T86KL.ChunkNNNN` (the tiling in end-point form, `leavesOKE`), and the energy chunks `T86K.EchkNNNN` over the
literal records of `T86K.ELits` (checked by `T86K.ELitsEq`), summed in `Trace86.EKR*`. They are composed with the
soundness theorems of the checker (the same as for `Trace86.LowerN`). No `native_decide` anywhere in the closure.
-/

open Set

namespace Trace86.Cert

open T86Core AuxCore AuxCommon

theorem FR_pos_K (x : ℝ) (hx : 0 < x) (hQx : ∀ j < 15, (QR (polys.getD j [])).eval x ≠ 0) : 0 < FR x := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hD0 : ((DEC * 2 ^ 0 : ℕ) : ℝ) = (DEC : ℝ) := by push_cast; ring
  rcases le_or_gt x ((10000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) with h1 | h1
  · have hl := T86Core.T86K.left_tail_ok
    rw [← T86Core.T86K.ctx_eq] at hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨hpre, hpos⟩ := hl
    have h := leftTailLB_sound IR_ge_K hpre hx h1 hQx
    have : (0 : ℝ) < (leftTailLB (mkCtx iLoNum 128) 10000000000 0 : ℝ) / 2 ^ P :=
      div_pos (by exact_mod_cast hpos) hP
    linarith
  · rcases lt_or_ge x ((30000000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) with h2 | h2
    · have hX0 : ((80000000000 : ℕ) / (DEC * 2 ^ 3 : ℕ) : ℝ) = ((10000000000 : ℕ) / (DEC * 2 ^ 0 : ℕ) : ℝ) := by
        norm_num [DEC]
      exact FR_pos_leaves_K IR_ge_K x ⟨by rw [hX0]; exact h1.le, h2⟩ hQx
    · have hr := T86Core.T86K.right_tail_ok
      rw [← T86Core.T86K.ctx_eq] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨hpre, hpos⟩ := hr
      rw [hD0] at h2
      have h := rightTailLB_sound IR_ge_K hpre h2 hQx
      have : (0 : ℝ) < (rightTailLB (mkCtx iLoNum 128) 30000000000000 : ℝ) / 2 ^ P :=
        div_pos (by exact_mod_cast hpos) hP
      linarith

/-- **The certificate (K).** -/
theorem certHyp_K : CertHyp Qc cR lamR NN eR GR sR :=
  certHyp_of (fun x hx hQx => (FR_pos_K x hx hQx).le)

theorem lamR_eq_K : lamR = lamL := by
  unfold lamR lamL
  norm_num [lamNum, lamDen]

end Trace86.Cert

namespace Trace86

open AuxCommon

theorem TPTraceLe_mono_K {B B' : ℝ} (h : B ≤ B') : TPTraceLe B ⊆ TPTraceLe B' := by
  rintro α ⟨hint, P, hP, hpos, hle⟩
  exact ⟨hint, P, hP, hpos, hle.trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))⟩

/-- **Lower bound (K).** For every `ε > 0`, only finitely many totally positive algebraic integers satisfy
`tr(α) ≤ (λ_L - ε) deg(α)`; that is, `C₈₆ ≥ λ_L`. -/
theorem trace_lower_K (ε : ℝ) (hε : 0 < ε) : (TPTraceLe (lamL - ε)).Finite := by
  have h := Cert.certHyp_K.trace_main energySmoothing ε hε
  rwa [Cert.lamR_eq_K] at h

/-- The decimal form (K). -/
theorem trace_lower_dec_K : (TPTraceLe (18022225 / 10000000)).Finite := by
  have hlt : (18022225 / 10000000 : ℝ) < lamL := by
    unfold lamL
    norm_num
  have h := trace_lower_K (lamL - 18022225 / 10000000) (by linarith)
  rwa [sub_sub_cancel] at h

end Trace86
