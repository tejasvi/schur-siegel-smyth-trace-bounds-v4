import Mathlib
import T86UCore.Leaves
import Trace86.Statement

/-!
# The 86a upper-bound certificate as real-valued objects (fork of `Trace86.CertDefs`)

The checker `T86UCore` works with integers; its soundness proof talks about the real objects defined here:

* `Qd l` the integer polynomial with descending coefficients `l` (`QR l` its image in `ℝ[X]`), `Qc j = Qd (polys j)`;
* `cR j = cwNum_j / 2^cwSh_j` (the weights `b_j`), `eR k = nodes_k / 10^12`, `rhoR k = rho_{k-1} / WD` (the weight `w_k`
  of the unit-mass hat at node `k`), `GR k = 2 w_k / (e_{k+1} - e_{k-1})` for `0 < k < NN` (`0` at the ends), `NN = 2324`;
* `CR i = -(slopeJump NN eR GR i) / 2` (the values of the checker's records), `UR x = ∑ CR i Hk(eR i - x)`, which is
  `-U_{μ₀}(x) / 2` for `μ₀ = G dx` by the closed form;
* `c0R = ε log(3/2) / (1 - ε)`, `FR x = c0R - ∑ cR j log |Q_j(x)| - 2 UR x` (`= U_{μ₀}(x) - ∑ b_j log|Q_j(x)| + c₀`).
-/

open Polynomial

namespace Trace86.UCert

open T86UCore

/-- The integer polynomial with descending coefficients `l` (Horner). -/
noncomputable def Qd (l : List Int) : ℤ[X] := l.foldl (fun acc a => acc * X + Polynomial.C a) 0

/-- Its image in `ℝ[X]`. -/
noncomputable def QR (l : List Int) : ℝ[X] := (Qd l).map (Int.castRingHom ℝ)

/-- The number of polynomials. -/
def JJ : ℕ := 21

/-- The certificate polynomials. -/
noncomputable def Qc (j : Fin JJ) : ℤ[X] := Qd (polys.getD j [])

/-- The weights. -/
noncomputable def cR (j : Fin JJ) : ℝ := (cwNum.getD j 0 : ℝ) / 2 ^ (cwSh.getD j 0)

/-- The last node index. -/
def NN : ℕ := 2324

/-- The nodes. -/
noncomputable def eR (k : ℕ) : ℝ := (nodes.getD k 0 : ℝ) / 10 ^ 12

/-- The weight `w_k` of the hat at node `k` (`0 < k < NN`). -/
noncomputable def rhoR (k : ℕ) : ℝ := (rho.getD (k - 1) 0 : ℝ) / WD

/-- The node values of `G = ∑ w_k h_k` (`h_k` the unit-mass hat on `[e_{k-1}, e_{k+1}]`, height `2/(e_{k+1} - e_{k-1})`). -/
noncomputable def GR (k : ℕ) : ℝ := if 0 < k ∧ k < NN then 2 * rhoR k / (eR (k + 1) - eR (k - 1)) else 0

/-- The values of the records: minus half the slope jumps of `G`. -/
noncomputable def CR (i : ℕ) : ℝ := -(slopeJump NN eR GR i) / 2

/-- `-U_{μ₀}/2` in closed form. -/
noncomputable def UR (x : ℝ) : ℝ := ∑ i ∈ Finset.range (NN + 1), CR i * Hk (eR i - x)

/-- `c₀ = ε log(3/2) / (1 - ε)`, `ε = EPSN / EPSD`. -/
noncomputable def c0R : ℝ := (EPSN : ℝ) * Real.log (3 / 2) / ((EPSD : ℝ) - EPSN)

/-- The function of condition (P): `U_{μ₀} - ∑ b_j log|Q_j| + c₀`. -/
noncomputable def FR (x : ℝ) : ℝ :=
  c0R - ∑ j : Fin JJ, cR j * Real.log |(QR (polys.getD j [])).eval x| - 2 * UR x

theorem Qd_map_eval {R : Type*} [CommRing R] (φ : ℤ →+* R) (l : List Int) (z : R) :
    ((Qd l).map φ).eval z = l.foldl (fun acc a => acc * z + φ a) 0 := by
  unfold Qd
  suffices h : ∀ (p : ℤ[X]), ((l.foldl (fun acc a => acc * X + Polynomial.C a) p).map φ).eval z =
      l.foldl (fun acc a => acc * z + φ a) ((p.map φ).eval z) by
    simpa using h 0
  induction l with
  | nil => intro p; simp
  | cons a t ih =>
    intro p
    simp only [List.foldl_cons]
    rw [ih (p * X + Polynomial.C a)]
    simp

theorem QR_eval_eq (l : List Int) (x : ℝ) :
    (QR l).eval x = l.foldl (fun (acc : ℝ) (a : ℤ) => acc * x + (a : ℝ)) 0 := by
  rw [QR, Qd_map_eval]
  simp

theorem foldl_ofReal (l : List Int) (x y : ℝ) :
    l.foldl (fun (acc : ℂ) (a : ℤ) => acc * (x : ℂ) + ((a : ℤ) : ℂ)) (y : ℂ) =
      ((l.foldl (fun (acc : ℝ) (a : ℤ) => acc * x + (a : ℝ)) y : ℝ) : ℂ) := by
  induction l generalizing y with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    push_cast
    ring_nf

theorem toC_eval_eq (l : List Int) (x : ℝ) :
    ‖(AuxCommon.toC (Qd l)).eval (x : ℂ)‖ = |(QR l).eval x| := by
  have h : (AuxCommon.toC (Qd l)).eval (x : ℂ) = (((QR l).eval x : ℝ) : ℂ) := by
    unfold AuxCommon.toC
    rw [Qd_map_eval, QR_eval_eq]
    have := foldl_ofReal l x 0
    simpa using this
  rw [h, Complex.norm_real, Real.norm_eq_abs]

end Trace86.UCert
