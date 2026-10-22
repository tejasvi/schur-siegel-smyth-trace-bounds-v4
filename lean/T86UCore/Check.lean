import AuxCore.LogK
import T86UCore.Data

/-!
# The checker for the 86a upper-bound certificate (core Lean only)

Fork of the lower-bound checker `T86Core.Check` for condition (P) of Lemma U1 of the paper: on `[0, 6]` off the roots,
`F(x) = U_{μ₀}(x) - ∑ b_j log|Q_j(x)| + c₀ ≥ 0`, `c₀ = ε log(3/2)/(1 - ε)`, `μ₀ = ∑ w_k h_k dx` (unit-mass hats). The
potential enters as `-2 U'` with the records `C'_i = -C_i/2` of `U' = -U_{μ₀}/2` (so the chord and window machinery is
the lower checker's), there is no main term, and the constant is `c₀` (field `isLo`; `m0hi = 0`). Also: the left tail
`(0, x₀]` (left of the support, `U_{μ₀}(x) ≥ U_{μ₀}(x₀)`), condition (M) (`∫ log|Q_j| dμ ≥ 0` from root brackets), the
budget (S) `∑ b_j deg Q_j < 1` and the trace (T).

Every quantity is an integer; real numbers appear only in the soundness proof. Scales: logarithms and values of `F` at
`2^P`; slope jumps at `2^QS`; a point is `x = X / D` with `D = 10^12 · 2^k`.
-/

namespace T86UCore

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

/-- Contributions of the hat `j` with weight `r / wd` on `[e_{j-1}, e_{j+1}]` (gaps `a = e_j - e_{j-1}`,
`b = e_{j+1} - e_j`, scale `DEC`) to `C'_{j-1}, C'_j, C'_{j+1}`, where `C' = -C/2` (`C`: the slope jumps of the density):
`-r DEC² / (wd a (a + b))`, `r DEC² / (wd a b)`, `-r DEC² / (wd b (a + b))`. -/
def hatL (wd r a b : Nat) : Int × Nat := (-((r * DEC * DEC : Nat) : Int), wd * a * (a + b))
def hatM (wd r a b : Nat) : Int × Nat := ((r * DEC * DEC : Nat), wd * a * b)
def hatR (wd r a b : Nat) : Int × Nat := (-((r * DEC * DEC : Nat) : Int), wd * b * (a + b))

/-- Consecutive gaps `[e_1 - e_0, …, e_N - e_{N-1}]`. -/
def gaps : List Nat → List Nat
  | n0 :: n1 :: ns => (n1 - n0) :: gaps (n1 :: ns)
  | _ => []

/-- The exact values `C'_0, …, C'_N` (as fractions), `C'_i = L_{i+1} + M_i + R_{i-1}`. -/
def hatC (wd : Nat) (ns rho : List Nat) : List (Int × Nat) :=
  let g := gaps ns
  let trip := List.zip rho (List.zip g (g.drop 1))
  let Ls := trip.map (fun t => hatL wd t.1 t.2.1 t.2.2)
  let Ms := trip.map (fun t => hatM wd t.1 t.2.1 t.2.2)
  let Rs := trip.map (fun t => hatR wd t.1 t.2.1 t.2.2)
  let z : Int × Nat := (0, 1)
  List.zipWith qadd (List.zipWith qadd (Ls ++ [z, z]) (z :: (Ms ++ [z]))) (z :: z :: Rs)

/-- Records `(n_i, sign C_i, ⌊2^q C_i⌋, ⌈2^q C_i⌉)`. -/
def mkRecsQ (q : Nat) (ns : List Nat) (cs : List (Int × Nat)) : List NRec :=
  List.zipWith (fun n c => ⟨n, Int.sign c.1, fdiv (c.1 * 2 ^ q) c.2, cdiv (c.1 * 2 ^ q) c.2⟩) ns cs

def mkRecs : List NRec := mkRecsQ QS nodes (hatC WD nodes rho)

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

/-- Global constants of a check: table, log 2, node records, `m0hi = 0`, lower bound `isLo` of `2^P c₀`. -/
structure Ctx where
  tab : Nat
  l2 : Nat × Nat
  rs : List NRec
  m0hi : Int
  isLo : Int
  sumC : Nat
deriving DecidableEq

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
      let Ap := base + pap - 2 * uHi (r.spl, r.sph) D
      let Aq := base + paq - 2 * uHi (r.sql, r.sqh) D
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
  c.isLo - c.m0hi + polyPart - 2 * (uHi S D + dU)

/-- A window must lie in `[0, 22]` (the constant `47` in `windowLB` bounds `|H'(e_i - x)|` for `|e_i - x| ≤ 22`). -/
def windowOK (c : Ctx) (Xu Xv k : Nat) : Bool :=
  decide (Xu < Xv) && decide (Xv ≤ 22 * (DEC * 2 ^ k)) && decide (0 < windowLB c Xu Xv k)

end T86UCore

namespace T86UCore

open AuxCore

/-! ## Global quantities and tails -/

/-- `c₀ = ε log(3/2) / (1 - ε) ≥ c0lo / 2^P` (`ε = EPSN / EPSD`). -/
def c0lo (tab : Nat) (l2 : Nat × Nat) : Int := fdiv ((EPSN : Int) * (logT tab l2 3 2).1) (EPSD - EPSN)

/-- The context of the upper check. -/
def mkCtx : Ctx :=
  let rs := mkRecs
  { tab := TAB, l2 := L2, rs := rs, m0hi := 0, isLo := c0lo TAB L2, sumC := sumAbsC rs }

/-- Left tail `(0, x₀]`, `x₀ = X0 / D ≤ 1`, `x₀` left of the support of `μ₀` (`leftTailPre`; so `U_{μ₀}` is decreasing on
`(-∞, x₀]`, `U_{μ₀}(x) ≥ U_{μ₀}(x₀)`, i.e. `-2 U'(x) ≥ -2 U'(x₀)`): `F ≥ c₀ - b_0 log x₀ - ∑_{j ≥ 1} b_j log B_j - 2 U'(x₀)`
(requires `Q_0 = x`). Lower bound at scale `2^P`. -/
def leftTailLB (c : Ctx) (X0 k : Nat) : Int :=
  let D : Nat := DEC * 2 ^ k
  let LD := logT c.tab c.l2 D 1
  let S := pointPass c.tab c.l2 c.rs k X0 LD
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

/-! ## Condition (M): `∫ log|Q_j| dμ ≥ 0` from root brackets

All roots of `Q_j` are real in `[0, 6]`, located in `deg Q_j` disjoint brackets `[l, u] / D` (`Q_j(l) Q_j(u) < 0`, or
`l = u` and `Q_j(l) = 0`). Then `∫ log|Q_j| dμ = ∑_r U_μ(r) = ∑_r ((1 - ε) U_{μ₀}(r) + ε log(3/2))`, which is
`≥ 0` if `∑_r (U_{μ₀}(r) + c₀) ≥ 0`; on a bracket `U_{μ₀} = -2 U' ≥ -2 (U'(l) + (u - l) · 47 ∑|C'_i|)`. -/

/-- `D^d Q(X / D)` (exact). -/
def polyVal (q : List Int) (X D : Nat) : Int := (taylorR X D q).headD 0

def bracketOK (q : List Int) (D : Nat) (b : Nat × Nat) : Bool :=
  if b.1 = b.2 then polyVal q b.1 D == 0
  else decide (b.1 < b.2) && decide (polyVal q b.1 D * polyVal q b.2 D < 0)

def bracketsOrdered : List (Nat × Nat) → Bool
  | b1 :: b2 :: bs => decide (b1.2 < b2.1) && bracketsOrdered (b2 :: bs)
  | _ => true

/-- Lower bound of `2^P ∑_r (U_{μ₀}(r) + c₀)` over the brackets. -/
def momentLB (c : Ctx) (k : Nat) (bs : List (Nat × Nat)) : Int :=
  let D : Nat := DEC * 2 ^ k
  let LD := logT c.tab c.l2 D 1
  bs.foldl (fun (acc : Int) (b : Nat × Nat) =>
    let S := pointPass c.tab c.l2 c.rs k b.1 LD
    let dU : Int := cdiv ((47 * c.sumC * (b.2 - b.1) : Nat) * 2 ^ P) (D * 2 ^ QS)
    acc + (c.isLo - c.m0hi - 2 * (uHi S D + dU))) 0

def momentOK (c : Ctx) (q : List Int) (k : Nat) (bs : List (Nat × Nat)) : Bool :=
  let D : Nat := DEC * 2 ^ k
  decide (bs.length = q.length - 1) && bracketsOrdered bs && bs.all (bracketOK q D) &&
    bs.all (fun b => decide (b.2 ≤ 6 * D)) && decide (0 < momentLB c k bs)

/-- (M) for all polynomials: `ms` lists `(k_j, brackets_j)` in the order of `polys`. -/
def momentsOK (c : Ctx) (ms : List (Nat × List (Nat × Nat))) : Bool :=
  decide (polys.length = ms.length) && (List.zip polys ms).all (fun t => momentOK c t.1 t.2.1 t.2.2)

/-! ## Irreducibility of the `Q_j` (for Lemma U1, step 2)

With all roots real in the brackets, a factor of `Q_j` of degree `0 < m < deg Q_j` would have an integer sum of roots
(it is monic up to sign); so it suffices that for every proper nonempty set of brackets the interval of possible root
sums contains no integer. -/

/-- No multiple of `D` in `[lo, hi]`. -/
def noIntIn (lo hi D : Nat) : Bool := decide (hi / D < (lo + D - 1) / D)

/-- All sublists (subsequences) of a list. -/
def subl {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => subl l ++ (subl l).map (a :: ·)

/-- For every sublist `t` of the brackets other than `[]` and the whole list, no integer lies in
`[∑_{t} l, ∑_{t} u] / D`. -/
def irredOK (k : Nat) (bs : List (Nat × Nat)) : Bool :=
  let D : Nat := DEC * 2 ^ k
  (subl bs).all (fun t => t.isEmpty || t.length == bs.length ||
    noIntIn (t.foldl (fun a b => a + b.1) 0) (t.foldl (fun a b => a + b.2) 0) D)

def irredsOK (ms : List (Nat × List (Nat × Nat))) : Bool := ms.all (fun t => irredOK t.1 t.2)

/-! ## Conditions (S) and (T) -/

/-- (S): `∑ b_j deg Q_j < 1`. -/
def budgetOK : Bool :=
  let S := cwSh.foldl max 0
  let lhs : Nat := (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ (S - x.2.2)) 0
  decide (lhs < 2 ^ S)

/-- `∑_k ρ_k (n_{k-1} + n_k + n_{k+1})` (the hat `k` has mean `(e_{k-1} + e_k + e_{k+1})/3`). -/
def traceNum : Nat :=
  (List.zip rho (List.zip nodes (List.zip (nodes.drop 1) (nodes.drop 2)))).foldl
    (fun acc t => acc + t.1 * (t.2.1 + t.2.2.1 + t.2.2.2)) 0

/-- (T): `(1 - ε) ∫ x dμ₀ + 3 ε = lamUNum / lamUDen`, i.e.
`(1 - ε) traceNum / (3 WD DEC) + 3 ε = λ_U` (exact). -/
def traceOK : Bool :=
  (EPSD - EPSN) * traceNum * lamUDen + 9 * EPSN * WD * DEC * lamUDen == 3 * WD * DEC * EPSD * lamUNum

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

/-- Sanity of the data: `Q_0 = x`, monic polynomials of degree `≥ 1`, positive weights, increasing nodes from `0` to `6`,
one hat weight per interior node, `∑ ρ_k = WD` (`μ₀` is a probability measure), `0 < ε < 1`. -/
def dataOK : Bool :=
  polys.headD [] == [1, 0] && polys.length == cwNum.length && polys.length == cwSh.length &&
  cwNum.all (fun c => decide (0 < c)) && polys.all (fun q => decide (2 ≤ q.length) && q.headD 0 == 1) &&
  rho.length + 2 == nodes.length && nodes.headD 1 == 0 && nodes.getLast?.getD 0 == 6 * DEC &&
  (List.zip nodes (nodes.drop 1)).all (fun x => decide (x.1 < x.2)) && rho.foldl (· + ·) 0 == WD &&
  decide (0 < EPSN) && decide (EPSN < EPSD)

end T86UCore
