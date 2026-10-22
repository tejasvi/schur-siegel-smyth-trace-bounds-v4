import AuxCommon.Basic

/-!
# The Schur–Siegel–Smyth trace constant: statements

The accompanying paper (Tao's constant 86a). For a totally positive algebraic integer `α` of degree `d` with conjugates
`α₁, …, α_d`, `tr(α) = α₁ + ⋯ + α_d`. The constant `C₈₆` is the lower limit of `tr(α)/deg(α)`: the largest `c` such
that for each `ε > 0` only finitely many totally positive algebraic integers satisfy `tr(α) < (c - ε) deg(α)`.

* Lower bound (certificate 915a52c7): `C₈₆ ≥ λ_L = 901111277/500000000 = 1.802222554`.
* Upper bound (certificate d773f831): `C₈₆ ≤ λ_U = 81383685642728309283453/45035996273705240000000 = 1.8070808325…`.

The constant itself is not defined through `sSup` (whose junk value would need a separate boundedness proof): the
lower bound is stated as the finiteness statement, the upper bound as the infinitude statement, which together are
`λ_L ≤ C₈₆ ≤ λ_U` in the sense of the paper.

The proved theorems are `Trace86.trace_lower_N`, `Trace86.trace_lower_dec_N` (Trace86/LowerN.lean; no hypotheses) and
`Trace86.trace_upper_N`, `Trace86.trace_upper_dec_N` (Trace86U/Upper.lean; one named hypothesis, `SmithThm15`).
-/

open Polynomial MeasureTheory Filter
open AuxCommon

namespace Trace86

/-! ## Totally positive algebraic integers and their traces -/

/-- All complex roots of `P` are positive real numbers. For a minimal polynomial of `α` this says that `α` is totally
positive. (Same text as in the companion Mahler-measure formalization.) -/
def AllRootsPos (P : ℤ[X]) : Prop :=
  ∀ z ∈ (toC P).roots, 0 < z.re ∧ z.im = 0

/-- The trace `tr(α)` of a root `α` of the minimal polynomial `P`: the sum of the complex roots of `P`, counted with
multiplicity (the conjugates of `α`; they are simple since `P` is irreducible). -/
noncomputable def traceP (P : ℤ[X]) : ℝ := ((toC P).roots.sum).re

/-- Totally positive algebraic integers `α` with `tr(α) ≤ B · deg(α)`. -/
def TPTraceLe (B : ℝ) : Set ℂ :=
  {α | IsIntegral ℤ α ∧ ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧ traceP P ≤ B * P.natDegree}

/-- The lower bound `λ_L = 901111277/500000000` of the paper (certificate 915a52c7). -/
noncomputable def lamL : ℝ := 901111277 / 500000000

/-- The upper bound `λ_U` of the paper (certificate d773f831). -/
noncomputable def lamU : ℝ := 81383685642728309283453 / 45035996273705240000000

/-! ## The reference densities: piecewise-linear functions and their closed forms
(same text as in the companion Mahler-measure formalization) -/

/-- The continuous piecewise-linear function with values `G k` at the nodes `e k` (`k ≤ N`), linear on each
`[e k, e (k+1)]` and `0` outside `[e 0, e N)`. -/
noncomputable def pwLin (N : ℕ) (e G : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    if e k ≤ x ∧ x < e (k + 1) then (G k * (e (k + 1) - x) + G (k + 1) * (x - e k)) / (e (k + 1) - e k) else 0

/-- Slope of `pwLin` on `[e k, e (k+1)]`. -/
noncomputable def slope (e G : ℕ → ℝ) (k : ℕ) : ℝ := (G (k + 1) - G k) / (e (k + 1) - e k)

/-- Jump `C_i` of the slope of `pwLin` at the node `e i` (the slope is `0` outside `[e 0, e N]`). -/
noncomputable def slopeJump (N : ℕ) (e G : ℕ → ℝ) (i : ℕ) : ℝ :=
  (if i < N then slope e G i else 0) - (if 0 < i ∧ i ≤ N then slope e G (i - 1) else 0)

/-- `H(t) = t²/2 log|t| - 3t²/4` (with `Real.log 0 = 0`, so `H 0 = 0`). -/
noncomputable def Hk (t : ℝ) : ℝ := t ^ 2 / 2 * Real.log |t| - 3 / 4 * t ^ 2

/-- `L(t) = t⁴/24 log|t| - 25t⁴/288`. -/
noncomputable def Lk (t : ℝ) : ℝ := t ^ 4 / 24 * Real.log |t| - 25 / 288 * t ^ 4

/-- Closed forms of the potential and energy of a piecewise-linear density (Lemma 3.1 of the companion Mahler-measure paper): for a piecewise-linear
`G` with `G 0 = G N = 0`, `U_ρ(x) = ∫ log|x - y| G(y) dy = ∑ᵢ Cᵢ H(eᵢ - x)` and
`I(ρ) = ∬ log|x - y| G(x) G(y) = ∑ᵢₖ Cᵢ Cₖ L(eᵢ - eₖ)`. Not a hypothesis: proved as `Trace86.pwLinClosedForm` (fork of
the companion formalization's proof). -/
def PwLinClosedForm : Prop :=
  ∀ (N : ℕ) (e G : ℕ → ℝ), (∀ k < N, e k < e (k + 1)) → G 0 = 0 → G N = 0 →
    (∀ x : ℝ, ∫ y, Real.log |x - y| * pwLin N e G y =
        ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x)) ∧
    (∫ x, ∫ y, Real.log |x - y| * pwLin N e G y * pwLin N e G x =
        ∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          slopeJump N e G i * slopeJump N e G k * Lk (e i - e k))

/-! ## The named hypothesis of the upper bound and the minimum principle (general facts of potential theory; no
certificate data) -/

/-- An integer polynomial viewed as a function on `ℝ`. -/
noncomputable abbrev evalR (Q : ℤ[X]) (x : ℝ) : ℝ := (Q.map (Int.castRingHom ℝ)).eval x

/-- **Named hypothesis (Smith, arXiv:2111.12660v2, Theorem 1.5, for an interval).** Let `b - a > 4` (the capacity
`(b - a)/4` of `[a, b]` exceeds `1`) and let `μ` be a Borel probability measure on `ℝ` supported in `[a, b]` such that
`∫ log |Q| dμ ≥ 0` for every nonzero `Q ∈ ℤ[X]` (Smith's condition (1); `log |Q|` is bounded above on `[a, b]`, and the
integral is `-∞` exactly when `μ` charges a root of `Q`, so (1) says: `μ` does not charge the roots of `Q`, `log |Q|` is
`μ`-integrable, and its integral is `≥ 0`; the first conjunct is needed because Mathlib's `Real.log 0 = 0`).
Then there are distinct irreducible monic `R_k ∈ ℤ[X]`, all of whose roots lie in `[a, b]`, whose root measures
`(1/deg R_k) ∑_{R_k(z) = 0} δ_z` converge weakly to `μ`. -/
def SmithThm15 : Prop :=
  ∀ a b : ℝ, 4 < b - a → ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc a b)ᶜ = 0 →
    (∀ Q : ℤ[X], Q ≠ 0 → μ {x | evalR Q x = 0} = 0 ∧ Integrable (fun x => Real.log |evalR Q x|) μ ∧
      0 ≤ ∫ x, Real.log |evalR Q x| ∂μ) →
    ∃ R : ℕ → ℤ[X], Function.Injective R ∧
      (∀ k, Irreducible (R k) ∧ (R k).Monic ∧ ∀ z ∈ (toC (R k)).roots, z.im = 0 ∧ a ≤ z.re ∧ z.re ≤ b) ∧
      ∀ f : ℝ → ℝ, Continuous f →
        Tendsto (fun k => ((toC (R k)).roots.map fun z => f z.re).sum / (R k).natDegree) atTop
          (nhds (∫ x, f x ∂μ))

/-- **Minimum principle (step 1 of Lemma U1 of the paper).** Not a hypothesis of the proved theorems: proved as
`Trace86.minPrinciple` (Trace86/MinPrincipleProof.lean). Let `μ` be a Borel probability measure
on `ℝ` supported in a compact interval `[a, b]` whose logarithmic potential `U_μ(z) = ∫ log|z - y| dμ(y)` is
continuous on `ℂ`. Let `Q₁, …, Q_m ∈ ℤ[X]` be nonzero with weights `b_j ≥ 0` and `∑ b_j deg Q_j < 1`, and put
`h(z) = U_μ(z) - ∑ b_j log|Q_j(z)|`. If `h(x) ≥ 0` at every `x ∈ [a, b]` that is not a root of any `Q_j`, then
`h(z) ≥ 0` at every `z ∈ ℂ` that is not a root of any `Q_j` (`h` is superharmonic off `[a, b]` and tends to `+∞` at
infinity). -/
def MinPrinciple : Prop :=
  ∀ a b : ℝ, a < b → ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc a b)ᶜ = 0 →
    Continuous (fun z : ℂ => ∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ) →
    ∀ (m : ℕ) (Q : Fin m → ℤ[X]) (w : Fin m → ℝ), (∀ j, Q j ≠ 0) → (∀ j, 0 ≤ w j) →
      ∑ j, w j * (Q j).natDegree < 1 →
      (∀ x : ℝ, a ≤ x → x ≤ b → (∀ j, evalR (Q j) x ≠ 0) →
        0 ≤ (∫ y, Real.log |x - y| ∂μ) - ∑ j, w j * Real.log |evalR (Q j) x|) →
      ∀ z : ℂ, (∀ j, (toC (Q j)).eval z ≠ 0) →
        0 ≤ (∫ y, Real.log ‖z - (y : ℂ)‖ ∂μ) - ∑ j, w j * Real.log ‖(toC (Q j)).eval z‖

end Trace86
