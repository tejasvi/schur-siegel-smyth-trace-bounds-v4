import AuxCore.LogK
import T86Core.Data

/-!
# The checker for the 86a lower-bound certificate (core Lean only)

Adapted from the companion Mahler-measure checker for the trace main term: the main term is `x` (instead of `log⁺ x`, so no
kink at `1`), the constant is `λ`, the slope jumps `C_i` come from the hat weights `ρ_k` (unit-mass hats), `s = ∑ ρ_k`,
nodes at scale `10^12`, left tail by the monotonicity of `U` left of the support, right tail for `x - κ' log x`, no
degree budget. The generic parts are unchanged.

Every quantity is an integer; real numbers appear only in the soundness proof (`Trace86.CheckSound*`, `Trace86.TailSound2`,
`Trace86.EnergySound`). Scales: logarithms and values of `F` at `2^P`; slope jumps `C_i` at `2^QS`; a point is
`x = X / D` with `D = 10^12 · 2^k`.

* `mkRecs` computes the node records `(n_i, sign C_i, ⌊2^QS C_i⌋, ⌈2^QS C_i⌉)` from the nodes and the hat weights.
* `chordOK` checks a chord leaf `[p, q]`: lower bounds `L(p), L(q) > 0` of the linear minorant
  `chord_A - M_A h^2/8 + T(x₀) + T'(x₀)(x - x₀)` of `F = A + T` on `[p, q]` (`T`: the convex polynomial terms selected
  by `mask`, with the tangent at `x₀ ∈ {p, q}`, plus the slope-jump terms of nodes at `p` or `q` with `C_i > 0`, which
  are `≥ 0`).
* `windowOK` checks a window `[u, v] ⊆ [0, 22]` (no smoothness needed: `|Q_j| ≤ B_j` on the window,
  `U ≤ U(u) + h · 47 ∑|C_i|`).
* `leftTailLB`/`leftTailPre` check `(0, x₀]`, `rightTailLB`/`rightTailPre` check `[x_hi, ∞)`.
-/

namespace T86Core

open AuxCore

/-! ## Constants -/

def P : Nat := 64
def QS : Nat := 64
def JT : Nat := 7
def WT : Nat := 66
def DEC : Nat := 1000000000000

/-- `mkTable 64 24 48 66` (checked by `tableCheck` in `Trace86.CheckSound`). -/
def TAB : Nat := mkTable 64 24 48 66
/-- Enclosure of `2^64 log 2`, rounded from `2^88` (checked by `l2Check` in `Trace86.CheckSound`). -/
def L2 : Nat × Nat := roundOut 24 (logRatK 88 48 2 1)

/-- `2^P log (a / b)`, enclosed. -/
def logT (tab : Nat) (l2 : Nat × Nat) (a b : Nat) : Int × Int :=
  logK P JT tab WT (Int.ofNat l2.1) (Int.ofNat l2.2) a b

/-! ## Integer interval helpers -/

/-- `⌊a / b⌋` for `b > 0`. -/
def fdiv (a : Int) (b : Nat) : Int := Int.ediv a (Int.ofNat b)
/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a : Int) (b : Nat) : Int := Int.neg (Int.ediv (Int.neg a) (Int.ofNat b))

/-- Interval product. -/
def imul (a b : Int × Int) : Int × Int :=
  let p1 := a.1 * b.1
  let p2 := a.1 * b.2
  let p3 := a.2 * b.1
  let p4 := a.2 * b.2
  (min (min p1 p2) (min p3 p4), max (max p1 p2) (max p3 p4))

/-! ## Node records -/

structure NRec where
  n : Nat
  sg : Int
  clo : Int
  chi : Int
deriving Repr, DecidableEq

/-- Rational sum `a/b + c/d` (`b, d > 0`). -/
def qadd (x y : Int × Nat) : Int × Nat := (x.1 * (y.2 : Int) + y.1 * (x.2 : Int), x.2 * y.2)

/-- Contributions of the hat `j` with weight `r / 2^rs` on `[e_{j-1}, e_{j+1}]` (gaps `a = e_j - e_{j-1}`,
`b = e_{j+1} - e_j`, scale `DEC`) to `C_{j-1}, C_j, C_{j+1}`: `2 r DEC² / (2^rs a (a + b))`, `-2 r DEC² / (2^rs a b)`,
`2 r DEC² / (2^rs b (a + b))`. -/
def hatL (rs r a b : Nat) : Int × Nat := ((2 * r * DEC * DEC : Nat), 2 ^ rs * a * (a + b))
def hatM (rs r a b : Nat) : Int × Nat := (-((2 * r * DEC * DEC : Nat) : Int), 2 ^ rs * a * b)
def hatR (rs r a b : Nat) : Int × Nat := ((2 * r * DEC * DEC : Nat), 2 ^ rs * b * (a + b))

/-- Consecutive gaps `[e_1 - e_0, …, e_N - e_{N-1}]`. -/
def gaps : List Nat → List Nat
  | n0 :: n1 :: ns => (n1 - n0) :: gaps (n1 :: ns)
  | _ => []

/-- The exact slope jumps `C_0, …, C_N` (as fractions) of `∑ ρ_k h_k`: `C_i = L_{i+1} + M_i + R_{i-1}`. -/
def hatC (rs : Nat) (ns rho : List Nat) : List (Int × Nat) :=
  let g := gaps ns
  let trip := List.zip rho (List.zip g (g.drop 1))
  let Ls := trip.map (fun t => hatL rs t.1 t.2.1 t.2.2)
  let Ms := trip.map (fun t => hatM rs t.1 t.2.1 t.2.2)
  let Rs := trip.map (fun t => hatR rs t.1 t.2.1 t.2.2)
  let z : Int × Nat := (0, 1)
  List.zipWith qadd (List.zipWith qadd (Ls ++ [z, z]) (z :: (Ms ++ [z]))) (z :: z :: Rs)

/-- Records `(n_i, sign C_i, ⌊2^q C_i⌋, ⌈2^q C_i⌉)`. -/
def mkRecsQ (q : Nat) (ns : List Nat) (cs : List (Int × Nat)) : List NRec :=
  List.zipWith (fun n c => ⟨n, Int.sign c.1, fdiv (c.1 * 2 ^ q) c.2, cdiv (c.1 * 2 ^ q) c.2⟩) ns cs

def mkRecs : List NRec := mkRecsQ QS nodes (hatC RS nodes rho)

/-- `∑ |C_i|` (upper bound, scale `2^QS`). -/
def sumAbsC (rs : List NRec) : Nat := rs.foldl (fun a r => a + max r.clo.natAbs r.chi.natAbs) 0

/-! ## The node pass of a chord leaf -/

/-- Accumulator: U-sums at `p` and `q` (scale `2^(P+QS+2)`, times `D^2`), the node part of `M` (scale `2^(P+QS)`),
and a flag for a node strictly inside `(p, q)`. -/
structure LAcc where
  spl : Int
  sph : Int
  sql : Int
  sqh : Int
  m : Int
  inside : Bool

/-- `4 · 2^P · Y = a² (2 (L - LD) - 3 · 2^P)` with `L = log a`, `LD = log D`: enclosure. -/
def yEncl (a : Nat) (L LD : Int × Int) : Int × Int :=
  let a2 : Int := (a * a : Nat)
  (a2 * (2 * (L.1 - LD.2) - 3 * 2 ^ P), a2 * (2 * (L.2 - LD.1) - 3 * 2 ^ P))

def leafStep (tab : Nat) (l2 : Nat × Nat) (k Xp Xq : Nat) (LD : Int × Int) (a : LAcc) (r : NRec) : LAcc :=
  if r.sg = 0 then a else
  let ni : Nat := r.n * 2 ^ k
  if Xp < ni ∧ ni < Xq then { a with inside := true } else
  let ap : Nat := if Xp ≤ ni then ni - Xp else Xp - ni
  let aq : Nat := if Xq ≤ ni then ni - Xq else Xq - ni
  let sing : Bool := decide (0 < r.sg) && (ap == 0 || aq == 0)
  if sing then a else
  let Lp := logT tab l2 ap 1
  let Lq := logT tab l2 aq 1
  let up := if ap = 0 then ((0 : Int), (0 : Int)) else imul (r.clo, r.chi) (yEncl ap Lp LD)
  let uq := if aq = 0 then ((0 : Int), (0 : Int)) else imul (r.clo, r.chi) (yEncl aq Lq LD)
  -- node part of M: upper bound of -2 C_i log|x - e_i| on [p, q]
  let vlo : Int := min Lp.1 Lq.1 - LD.2
  let vhi : Int := (if ap = 0 then Lq.2 else if aq = 0 then Lp.2 else max Lp.2 Lq.2) - LD.1
  let mt : Int :=
    if 0 < r.sg then -2 * (if 0 ≤ vlo then r.clo * vlo else r.chi * vlo)
    else 2 * (if 0 ≤ vhi then (-r.clo) * vhi else (-r.chi) * vhi)
  ⟨a.spl + up.1, a.sph + up.2, a.sql + uq.1, a.sqh + uq.2, a.m + mt, a.inside⟩

def leafPass (tab : Nat) (l2 : Nat × Nat) (rs : List NRec) (k Xp Xq : Nat) (LD : Int × Int) : LAcc :=
  rs.foldl (leafStep tab l2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩

/-! ## Point pass (windows and tails): upper bound of the U-sum at one point -/

def pointStep (tab : Nat) (l2 : Nat × Nat) (k X : Nat) (LD : Int × Int) (a : Int × Int) (r : NRec) : Int × Int :=
  if r.sg = 0 then a else
  let ni : Nat := r.n * 2 ^ k
  let ad : Nat := if X ≤ ni then ni - X else X - ni
  if ad = 0 then a else
  let u := imul (r.clo, r.chi) (yEncl ad (logT tab l2 ad 1) LD)
  (a.1 + u.1, a.2 + u.2)

def pointPass (tab : Nat) (l2 : Nat × Nat) (rs : List NRec) (k X : Nat) (LD : Int × Int) : Int × Int :=
  rs.foldl (pointStep tab l2 k X LD) (0, 0)

/-- Upper bound of `2^P U` from the U-sum (scale `2^(P+QS+2)`, times `D^2`). -/
def uHi (S : Int × Int) (D : Nat) : Int := cdiv S.2 (D * D * 2 ^ (QS + 2))

/-! ## Polynomials -/

/-- `(v + X) r` for an ascending coefficient list `r`. -/
def mulVX (X : Int) : List Int → List Int
  | [] => []
  | r0 :: rs => X * r0 :: addHead r0 (mulVX X rs)
where
  addHead (c : Int) : List Int → List Int
    | [] => [c]
    | h :: t => (c + h) :: t

/-- Ascending coefficients of `R(v) = D^d Q((X + v)/D)` from the descending coefficients of `Q`. -/
def taylorR (X D : Nat) (desc : List Int) : List Int :=
  (desc.foldl (fun (st : List Int × Int) a =>
    match st with
    | (r, dp) => (match mulVX (X : Int) r with
                  | [] => [a * dp]
                  | h :: t => (h + a * dp) :: t, dp * (D : Int))) ([], 1)).1

/-- `∑ γ_n H^n` (ascending list). -/
def evalAsc (H : Int) (g : List Int) : Int := g.foldr (fun c acc => c + H * acc) 0

/-- `∑_{n ≥ 1} |γ_n| H^n`. -/
def tailAbs (H : Nat) : List Int → Nat
  | [] => 0
  | _ :: t => H * (t.foldr (fun c acc => c.natAbs + H * acc) 0)

/-- Derivative of an ascending coefficient list. -/
def derivAsc (g : List Int) : List Int :=
  (g.drop 1).zipIdx.map (fun (c, i) => c * ((i + 1 : Nat) : Int))

/-- Enclosure of a polynomial (ascending) on `[0, H]` (one-sided: negative terms lower the lower end, positive terms
raise the upper end). -/
def encl (H : Nat) (g : List Int) : Int × Int :=
  match g with
  | [] => (0, 0)
  | c0 :: t =>
    (t.zipIdx.foldl (fun (acc : Int × Int) (q : Int × Nat) =>
      let v : Int := q.1 * (H : Int) ^ (q.2 + 1)
      if v < 0 then (acc.1 + v, acc.2) else (acc.1, acc.2 + v)) (c0, c0))

/-- `-c log |W / D^d|` lower bound at scale `2^P`, with `c = cn / 2^cs`. -/
def mcLogLo (tab : Nat) (l2 : Nat × Nat) (cn cs d : Nat) (W : Int) (LD : Int × Int) : Int :=
  fdiv (-(cn : Int) * ((logT tab l2 W.natAbs 1).2 - (d : Int) * LD.1)) (2 ^ cs)

/-- Per-polynomial data of a chord leaf: `none` if the polynomial may vanish on `[p, q]` or is required convex but is
not; otherwise `(add to A(p), add to A(q), add to T(x₀), slope term, M part)`, all lower bounds at scale `2^P` except the
`M` part (upper bound, scale `2^P`, already multiplied by `h²`). -/
def polyLeaf (tab : Nat) (l2 : Nat × Nat) (Xp Xq D : Nat) (LD : Int × Int) (x0q conv : Bool)
    (desc : List Int) (cn cs : Nat) : Option (Int × Int × Int × Int × Int) :=
  let H : Nat := Xq - Xp
  let d : Nat := desc.length - 1
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let b2 := derivAsc b1
  let R0 := encl H b
  let R1 := encl H b1
  let R2 := encl H b2
  let W0 := b.headD 0
  let Wq := evalAsc (H : Int) b
  let ex0 : Bool := decide (0 < R0.1) || decide (R0.2 < 0)
  -- `R'` has no zero on `[0, H]`: `R` is strictly monotone there
  let mono : Bool := decide (0 < R1.1) || decide (R1.2 < 0)
  if ex0 || (mono && decide (0 < W0 * Wq)) then
    let sq := imul R1 R1
    let sqlo : Int := if 0 ≤ R1.1 * R1.2 then max sq.1 0 else 0
    let RR := imul R0 R2
    if conv then
      if 0 ≤ sqlo - RR.2 then
        if x0q then
          let R1H := evalAsc (H : Int) b1
          let sl : Int := if 0 < Wq then fdiv ((cn : Int) * R1H * (H : Int) * 2 ^ P) (Wq.natAbs * 2 ^ cs)
                          else fdiv (-(cn : Int) * R1H * (H : Int) * 2 ^ P) (Wq.natAbs * 2 ^ cs)
          some (0, 0, mcLogLo tab l2 cn cs d Wq LD, sl, 0)
        else
          let R10 := b1.headD 0
          let sl : Int := if 0 < W0 then fdiv (-(cn : Int) * R10 * (H : Int) * 2 ^ P) (W0.natAbs * 2 ^ cs)
                          else fdiv ((cn : Int) * R10 * (H : Int) * 2 ^ P) (W0.natAbs * 2 ^ cs)
          some (0, 0, mcLogLo tab l2 cn cs d W0 LD, sl, 0)
      else none
    else
      let Nhi : Int := sq.2 - RR.1
      let r1 : Nat := if ex0 then min R0.1.natAbs R0.2.natAbs else 0
      let rmin : Nat := if mono then max r1 (min W0.natAbs Wq.natAbs) else r1
      let mp : Int := if 0 < Nhi then cdiv ((cn : Int) * (H : Int) * (H : Int) * Nhi * 2 ^ P) (rmin * rmin * 2 ^ cs)
                      else 0
      some (mcLogLo tab l2 cn cs d W0 LD, mcLogLo tab l2 cn cs d Wq LD, 0, 0, mp)
  else none

/-! ## Leaf checks -/

/-- Global constants of a check: table, log 2, node records, `⌈2^P λ⌉` (field `m0hi`), lower bound of `2^P I/s`. -/
structure Ctx where
  tab : Nat
  l2 : Nat × Nat
  rs : List NRec
  m0hi : Int
  isLo : Int
  sumC : Nat
deriving DecidableEq

/-- Lower bound of `2^P x` for `x = X / D` (the main term). -/
def mainLo (X D : Nat) : Int := fdiv ((X : Int) * 2 ^ P) D

/-- Lower bounds `(L(p), L(q))` of a chord leaf, or `none`. -/
def chordLB (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) : Option (Int × Int) :=
  let D : Nat := DEC * 2 ^ k
  let H : Nat := Xq - Xp
  if Xp < Xq ∧ H ≤ D then
    let LD := logT c.tab c.l2 D 1
    let r := leafPass c.tab c.l2 c.rs k Xp Xq LD
    if r.inside then none else
    let base : Int := c.isLo - c.m0hi
    let polyRes := (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
      (fun (acc : Option (Int × Int × Int × Int × Int)) (x : (List Int × Nat × Nat) × Nat) =>
        match acc with
        | none => none
        | some (ap, aq, t0, sl, mp) =>
          match polyLeaf c.tab c.l2 Xp Xq D LD x0q (Nat.testBit mask x.2) x.1.1 x.1.2.1 x.1.2.2 with
          | none => none
          | some (ap', aq', t0', sl', mp') => some (ap + ap', aq + aq', t0 + t0', sl + sl', mp + mp'))
      (some (0, 0, 0, 0, 0))
    match polyRes with
    | none => none
    | some (pap, paq, t0, sl, mp) =>
      let Ap := mainLo Xp D + base + pap - 2 * uHi (r.spl, r.sph) D
      let Aq := mainLo Xq D + base + paq - 2 * uHi (r.sql, r.sqh) D
      let mn : Int := if 0 < r.m then cdiv (r.m * (H : Int) * (H : Int)) (D * D * 2 ^ QS) else 0
      let corr : Int := cdiv (mn + mp) 8
      if x0q then some (Ap + t0 + sl - corr, Aq + t0 - corr)
      else some (Ap + t0 - corr, Aq + t0 + sl - corr)
  else none

def chordOK (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) : Bool :=
  match chordLB c Xp Xq k x0q mask with
  | some (lp, lq) => decide (0 < lp) && decide (0 < lq)
  | none => false

/-- Lower bound of `F` on the window `[Xu, Xv] / D` (scale `2^P`). -/
def windowLB (c : Ctx) (Xu Xv k : Nat) : Int :=
  let D : Nat := DEC * 2 ^ k
  let H : Nat := Xv - Xu
  let LD := logT c.tab c.l2 D 1
  let S := pointPass c.tab c.l2 c.rs k Xu LD
  let polyPart := (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun (acc : Int) (x : List Int × Nat × Nat) =>
      let R0 := encl H (taylorR Xu D x.1)
      let B : Nat := max R0.1.natAbs R0.2.natAbs
      acc + fdiv (-(x.2.1 : Int) * ((logT c.tab c.l2 B 1).2 - ((x.1.length - 1 : Nat) : Int) * LD.1)) (2 ^ x.2.2))
    0
  let dU : Int := cdiv ((47 * c.sumC * H : Nat) * 2 ^ P) (D * 2 ^ QS)
  mainLo Xu D - c.m0hi + c.isLo + polyPart - 2 * (uHi S D + dU)

/-- A window must lie in `[0, 22]` (the constant `47` in `windowLB` bounds `|H'(e_i - x)|` for `|e_i - x| ≤ 22`). -/
def windowOK (c : Ctx) (Xu Xv k : Nat) : Bool :=
  decide (Xu < Xv) && decide (Xv ≤ 22 * (DEC * 2 ^ k)) && decide (0 < windowLB c Xu Xv k)

end T86Core

namespace T86Core

open AuxCore

/-! ## Global quantities and tails -/

/-- `s = sNum / sDen = ∑ ρ_k` (unit-mass hats). -/
def sNum : Nat := rho.foldl (· + ·) 0
def sDen : Nat := 2 ^ RS

/-- Context with the claimed lower bound `I ≥ iNum / 2^iSh` of the energy `I(ρ)`. -/
def mkCtx (iNum : Int) (iSh : Nat) : Ctx :=
  let rs := mkRecs
  { tab := TAB, l2 := L2, rs := rs, m0hi := cdiv ((lamNum : Int) * 2 ^ P) lamDen,
    isLo := fdiv (iNum * (sDen : Int) * 2 ^ P) (sNum * 2 ^ iSh), sumC := sumAbsC rs }

/-- Left tail `(0, x₀]`, `x₀ = X0 / D ≤ 1`, `x₀` left of the support of `ρ` (`leftTailPre`; so `U` is decreasing on
`[0, x₀]`, `U(x) ≤ U(0)`): `F ≥ 0 - λ - c₀ log x₀ - ∑_{j ≥ 1} c_j log B_j - 2 U(0) + I/s` (requires `Q_0 = x`).
Lower bound at scale `2^P`. -/
def leftTailLB (c : Ctx) (X0 k : Nat) : Int :=
  let D : Nat := DEC * 2 ^ k
  let LD := logT c.tab c.l2 D 1
  let S := pointPass c.tab c.l2 c.rs k 0 LD
  let polyPart := (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
    (fun (acc : Int) (x : (List Int × Nat × Nat) × Nat) =>
      if x.2 = 0 then
        acc + fdiv (-(x.1.2.1 : Int) * (logT c.tab c.l2 X0 D).2) (2 ^ x.1.2.2)
      else
        let R0 := encl X0 (taylorR 0 D x.1.1)
        let B : Nat := max R0.1.natAbs R0.2.natAbs
        acc + fdiv (-(x.1.2.1 : Int) * ((logT c.tab c.l2 B 1).2 - ((x.1.1.length - 1 : Nat) : Int) * LD.1))
          (2 ^ x.1.2.2))
    0
  c.isLo - c.m0hi + polyPart - 2 * uHi S D

/-- The left tail is left of the support: `ρ_j = 0` for every hat `j` with `e_{j-1} < x₀`, and `0 < x₀ ≤ 1`
(`rho[j-1]` is paired with `nodes[j-1] = e_{j-1}`). -/
def leftTailPre (X0 k : Nat) : Bool :=
  decide (0 < X0) && decide (X0 ≤ DEC * 2 ^ k) &&
    (List.zip rho nodes).all (fun t => t.1 == 0 || decide (X0 ≤ t.2 * 2 ^ k))

/-- Right tail `[x_t, ∞)`, `x_t = Xt / 10^12 ≥ max(1, e_N, κ')` with `κ' = ∑ c_j deg_j + 2 s`: for `x ≥ x_t`,
`|Q_j(x)| ≤ x^{d_j} A_j` with `A_j = ∑_n |a_n| x_t^{-n}`, and `U(x) ≤ s log x`, so
`F(x) ≥ x - κ' log x - b ≥ x_t - κ' log x_t - b` (`x - κ' log x` increases for `x ≥ κ'`), `b = λ - I/s + ∑ c_j log A_j`.
Lower bound of `2^P (x_t - κ' log x_t - b)`. -/
def rightTailLB (c : Ctx) (Xt : Nat) : Int :=
  let lx := logT c.tab c.l2 Xt DEC
  let S := cwSh.foldl max 0
  let kDen : Nat := 2 ^ S * sDen
  let kNum : Nat := (List.zip polys (List.zip cwNum cwSh)).foldl
      (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ (S - x.2.2) * sDen) 0 + 2 * sNum * 2 ^ S
  let klog : Int := cdiv ((kNum : Int) * lx.2) kDen
  let aPart := (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun (acc : Int) (x : List Int × Nat × Nat) =>
      let d : Nat := x.1.length - 1
      let num : Nat := x.1.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (d - q.2)) 0
      acc + fdiv (-(x.2.1 : Int) * (logT c.tab c.l2 num (Xt ^ d)).2) (2 ^ x.2.2))
    0
  mainLo Xt DEC - klog - c.m0hi + c.isLo + aPart

/-- Preconditions of the right tail: `x_t ≥ 1`, `x_t ≥ e_N` and `x_t ≥ κ'` (exact). -/
def rightTailPre (Xt : Nat) : Bool :=
  let S := cwSh.foldl max 0
  let kDen : Nat := 2 ^ S * sDen
  let kNum : Nat := (List.zip polys (List.zip cwNum cwSh)).foldl
      (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ (S - x.2.2) * sDen) 0 + 2 * sNum * 2 ^ S
  decide (DEC ≤ Xt) && decide (nodes.getLast?.getD 0 ≤ Xt) && decide (kNum * DEC ≤ Xt * kDen)

/-! ## The energy `I(ρ)` (shards by blocks of rows)

`I = ∑_{i,k} C_i C_k L(e_i - e_k) = (1 / (12 · 10^48)) ∑_{i < k} C_i C_k V_ik` with
`V_ik = d⁴ (log d - log 10^12 - 25/12)`, `d = n_k - n_i` (the nodes are increasing). Scales: `C` at `2^QI`, logarithms at
`2^PI`, terms at `2^(2 QI + PI)`. -/

def PI : Nat := 100
def QI : Nat := 100
def JI : Nat := 10
def WI : Nat := 102
/-- `mkTable 100 24 48 102` (checked by `tableCheck` in `Trace86.EnergySound`). -/
def TABI : Nat := mkTable 100 24 48 102
def L2I : Nat × Nat := roundOut 24 (logRatK 124 48 2 1)

def logI (tab : Nat) (l2 : Nat × Nat) (a b : Nat) : Int × Int :=
  logK PI JI tab WI (Int.ofNat l2.1) (Int.ofNat l2.2) a b

def recsI : List NRec := mkRecsQ QI nodes (hatC RS nodes rho)

/-- `∑_{k} C_i C_k V_ik` over the records `rest` following `ri` (enclosure at scale `2^(2 QI + PI)`). -/
def iRow (tab : Nat) (l2 : Nat × Nat) (lDec : Int × Int) (ri : NRec) (rest : List NRec) : Int × Int :=
  let c25lo : Int := fdiv (25 * 2 ^ PI) 12
  let c25hi : Int := cdiv (25 * 2 ^ PI) 12
  rest.foldl (fun (acc : Int × Int) (rk : NRec) =>
    if rk.sg = 0 then acc else
    let d : Nat := rk.n - ri.n
    let L := logI tab l2 d 1
    let d4 : Int := ((d * d) * (d * d) : Nat)
    let t := imul (imul (ri.clo, ri.chi) (rk.clo, rk.chi)) (d4 * (L.1 - lDec.2 - c25hi), d4 * (L.2 - lDec.1 - c25lo))
    (acc.1 + t.1, acc.2 + t.2)) (0, 0)

/-- The rows `rs` (with their tails): `∑` of `iRow` over the first `cnt` records of `rs`. -/
def iBlockAux (tab : Nat) (l2 : Nat × Nat) (lDec : Int × Int) : Nat → List NRec → Int × Int → Int × Int
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | cnt + 1, r :: rest, acc =>
    let t := if r.sg = 0 then ((0 : Int), (0 : Int)) else iRow tab l2 lDec r rest
    iBlockAux tab l2 lDec cnt rest (acc.1 + t.1, acc.2 + t.2)

/-- Enclosure of `∑_{i0 ≤ i < i0 + cnt} ∑_{k > i} C_i C_k V_ik` (scale `2^(2 QI + PI)`). -/
def iBlock (i0 cnt : Nat) : Int × Int :=
  let tab := TABI
  let l2 := L2I
  iBlockAux tab l2 (logI tab l2 DEC 1) cnt (recsI.drop i0) (0, 0)

/-! ## Leaves, coverage, the complete check -/

/-- A leaf: `kind = 0` chord `[X1, X2] / D` (with `x0q`, `mask`), `kind = 1` window. -/
structure Leaf where
  kind : Nat
  X1 : Nat
  X2 : Nat
  k : Nat
  x0q : Bool
  mask : Nat
deriving Repr, DecidableEq

def leafOK (c : Ctx) (l : Leaf) : Bool :=
  if l.kind = 0 then chordOK c l.X1 l.X2 l.k l.x0q l.mask else windowOK c l.X1 l.X2 l.k

/-- `a / (10^12 2^ka) = b / (10^12 2^kb)`. -/
def ptEq (a ka b kb : Nat) : Bool := a * 2 ^ kb == b * 2 ^ ka

/-- The leaves tile `[X0 / D0, XT / DT]` in order (consecutive end points equal) and each passes. -/
def leavesOK (c : Ctx) : Nat → Nat → List Leaf → Nat → Nat → Bool
  | X, kx, [], XT, kT => ptEq X kx XT kT
  | X, kx, l :: ls, XT, kT => ptEq X kx l.X1 l.k && leafOK c l && leavesOK c l.X2 l.k ls XT kT

/-- Sanity of the data: `Q_0 = x`, positive weights, polynomials of degree `≥ 1`, increasing nodes, one hat weight per
interior node, `s > 0`. -/
def dataOK : Bool :=
  polys.headD [] == [1, 0] && polys.length == cwNum.length && polys.length == cwSh.length &&
  cwNum.all (fun c => decide (0 < c)) && polys.all (fun q => decide (2 ≤ q.length) && decide (q.headD 0 ≠ 0)) &&
  rho.length + 2 == nodes.length &&
  (List.zip nodes (nodes.drop 1)).all (fun x => decide (x.1 < x.2)) && decide (0 < sNum)

end T86Core
