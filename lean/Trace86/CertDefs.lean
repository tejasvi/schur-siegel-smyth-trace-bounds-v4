import Mathlib
import T86Core.Leaves
import Trace86.Statement

/-!
# The 86a lower-bound certificate as real-valued objects (adapted from the companion Mahler-measure formalization)

The checker `T86Core` works with integers; its soundness proof talks about the real objects defined here, which are those
of `Trace86.Assembly.CertHyp`:

* `Qd l` the integer polynomial with descending coefficients `l` (`QR l` its image in `ℝ[X]`), `Qc j = Qd (polys j)`;
* `cR j = cwNum_j / 2^cwSh_j`, `eR k = nodes_k / 10^12`, `rhoR k = rho_{k-1} / 2^RS` (hat at node `k`),
  `GR k = 2 ρ_k / (e_{k+1} - e_{k-1})` for `0 < k < NN` (`0` at the ends: `G = ∑ ρ_k h_k` with unit-mass hats),
  `NN = 10387`, `sR = sNum / sDen = ∑ ρ_k`, `lamR = λ`;
* `CR i = slopeJump NN eR GR i`, `UR x = ∑ CR i Hk(eR i - x)`, `IR = ∑∑ CR i CR k Lk(eR i - eR k)`;
* `FR x = x - λ - ∑ cR j log |Q_j(x)| - 2 UR x + IR / sR`.
-/

open Polynomial

namespace Trace86.Cert

open T86Core

/-- The integer polynomial with descending coefficients `l` (Horner). -/
noncomputable def Qd (l : List Int) : ℤ[X] := l.foldl (fun acc a => acc * X + Polynomial.C a) 0

/-- Its image in `ℝ[X]`. -/
noncomputable def QR (l : List Int) : ℝ[X] := (Qd l).map (Int.castRingHom ℝ)

/-- The number of polynomials (with positive weight). -/
def JJ : ℕ := 15

/-- The certificate polynomials. -/
noncomputable def Qc (j : Fin JJ) : ℤ[X] := Qd (polys.getD j [])

/-- The weights. -/
noncomputable def cR (j : Fin JJ) : ℝ := (cwNum.getD j 0 : ℝ) / 2 ^ (cwSh.getD j 0)

/-- The last node index. -/
def NN : ℕ := 10387

/-- The nodes. -/
noncomputable def eR (k : ℕ) : ℝ := (nodes.getD k 0 : ℝ) / 10 ^ 12

/-- The weight of the hat at node `k` (`0 < k < NN`). -/
noncomputable def rhoR (k : ℕ) : ℝ := (rho.getD (k - 1) 0 : ℝ) / 2 ^ RS

/-- The node values of `G = ∑ ρ_k h_k` (`h_k` the unit-mass hat on `[e_{k-1}, e_{k+1}]`, height `2/(e_{k+1} - e_{k-1})`). -/
noncomputable def GR (k : ℕ) : ℝ := if 0 < k ∧ k < NN then 2 * rhoR k / (eR (k + 1) - eR (k - 1)) else 0

/-- `λ`. -/
noncomputable def lamR : ℝ := (lamNum : ℝ) / lamDen

/-- The mass `s`. -/
noncomputable def sR : ℝ := (sNum : ℝ) / sDen

/-- The slope jumps. -/
noncomputable def CR (i : ℕ) : ℝ := slopeJump NN eR GR i

/-- The potential in closed form. -/
noncomputable def UR (x : ℝ) : ℝ := ∑ i ∈ Finset.range (NN + 1), CR i * Hk (eR i - x)

/-- The energy in closed form. -/
noncomputable def IR : ℝ :=
  ∑ i ∈ Finset.range (NN + 1), ∑ k ∈ Finset.range (NN + 1), CR i * CR k * Lk (eR i - eR k)

/-- The auxiliary function. -/
noncomputable def FR (x : ℝ) : ℝ :=
  x - lamR - ∑ j : Fin JJ, cR j * Real.log |(QR (polys.getD j [])).eval x| - 2 * UR x + IR / sR

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

end Trace86.Cert
