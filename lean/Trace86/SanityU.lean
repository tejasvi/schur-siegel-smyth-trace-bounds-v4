import Trace86.Statement

/-!
# Sanity checks of the `SmithThm15` premise (not part of any proof)

Without the conjunct `μ {x | evalR Q x = 0} = 0` the premise would admit `μ = δ₀`: with `Real.log 0 = 0`,
`∫ log |Q| dδ₀ = log |Q(0)| ≥ 0` for every nonzero `Q ∈ ℤ[X]`. With it, `δ₀` is not admissible: for `Q = X`,
`δ₀ {x | evalR X x = 0} = 1 ≠ 0`.
More generally no measure with an atom at an algebraic number is admissible (take `Q` its minimal polynomial).
-/

open Polynomial MeasureTheory

namespace Trace86.Sanity

open AuxCommon

/-- `δ₀` fails the premise (at `Q = X`). -/
theorem dirac_zero_not_admissible :
    ¬ (∀ Q : ℤ[X], Q ≠ 0 → (Measure.dirac (0 : ℝ)) {x | evalR Q x = 0} = 0 ∧
        Integrable (fun x => Real.log |evalR Q x|) (Measure.dirac (0 : ℝ)) ∧
        0 ≤ ∫ x, Real.log |evalR Q x| ∂(Measure.dirac (0 : ℝ))) := by
  intro h
  have h1 := (h X X_ne_zero).1
  have hmem : (0 : ℝ) ∈ {x : ℝ | evalR X x = 0} := by simp [evalR]
  rw [Measure.dirac_apply_of_mem hmem] at h1
  exact one_ne_zero h1

/-- More generally: an atom at a root of a nonzero `Q` makes the premise fail. -/
theorem atom_at_root_not_admissible (μ : Measure ℝ) {Q : ℤ[X]} (hQ : Q ≠ 0) {t : ℝ} (ht : evalR Q t = 0)
    (hatom : μ {t} ≠ 0) :
    ¬ (∀ P : ℤ[X], P ≠ 0 → μ {x | evalR P x = 0} = 0 ∧ Integrable (fun x => Real.log |evalR P x|) μ ∧
        0 ≤ ∫ x, Real.log |evalR P x| ∂μ) := by
  intro h
  have h1 := (h Q hQ).1
  apply hatom
  exact measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact ht) h1

end Trace86.Sanity
