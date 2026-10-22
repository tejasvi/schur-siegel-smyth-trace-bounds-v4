import T86Core.Check

/-!
# End-point node data and the second-order curvature bound for chord leaves

A chord leaf `[p, q]` (no node with `C_i ≠ 0` strictly inside) needs from the nodes: upper bounds of `U(p)` and `U(q)`
and an upper bound `M` of the node part `-2 ∑ C_i log |x - e_i|` of the curvature on `(p, q)`. Here every node quantity
is a sum at one end point, computed once per point (`epData`, at the reduced scale of `canon`) and shared by the two
leaves that meet there:

* `uhi`: upper bound of `2^P U(x)` (as `uHi ∘ pointPass`);
* `g0`: lower bound of `2^(P+QS) ∑_{e_i ≠ x} C_i log |x - e_i|`;
* `kl`, `kr`: upper bounds of `2^QS ∑ 2 |C_i| / (x - e_i)²` over the nodes with `C_i < 0` left resp. right of `x`;
* `cl`, `cle`: the numbers of nodes with `C_i ≠ 0` and `e_i < x` resp. `e_i ≤ x`;
* `apl, aph` (`anl, anh`): sums of `⌊2^QS C_i⌋, ⌈2^QS C_i⌉` over the nodes at `x` with `C_i > 0` (`C_i < 0`).

For the leaf, with `R` the nodes outside `[p, q]` and `g_R(x) = ∑_R C_i log |x - e_i|`: `-2 g_R'' = 2 ∑_R C_i / (x - e_i)²
≥ -K` with `K = 2 ∑_{R, C_i < 0} |C_i| / dist(e_i, [p, q])²`, so `-2 g_R(x) ≤ max(-2 g_R(p), -2 g_R(q)) + K h² / 8` on
`[p, q]`; the nodes at `p` or `q` with `C_i < 0` add at most `2 |C_i| log h`, those with `C_i > 0` are the singular terms
(`≥ 0`) of `chordLB`. The rest of the leaf check is that of `chordLB`.
-/

namespace T86Core

open AuxCore

/-- `(X, k)` with factors `2` removed from `X` while `k > 0` (the same point `X / (10^12 2^k)`). -/
def canon : Nat → Nat → Nat × Nat
  | X, 0 => (X, 0)
  | X, k + 1 => if X % 2 = 0 then canon (X / 2) k else (X, k + 1)

/-- Accumulator of the end-point pass. -/
structure EAcc where
  s : Int × Int
  g0 : Int
  kl : Int
  kr : Int
  cl : Nat
  cle : Nat
  apl : Int
  aph : Int
  anl : Int
  anh : Int

/-- Node data at a point (see the module docstring). -/
structure EPt where
  uhi : Int
  g0 : Int
  kl : Int
  kr : Int
  cl : Nat
  cle : Nat
  apl : Int
  aph : Int
  anl : Int
  anh : Int
deriving Repr, DecidableEq

/-- One node of the end-point pass at `x = X / D`, `D = 10^12 2^k`, `DD = D²`. The U-sum is that of `pointStep`. -/
def epStep (tab : Nat) (l2 : Nat × Nat) (k X : Nat) (DD : Int) (LD : Int × Int) (a : EAcc) (r : NRec) : EAcc :=
  if r.sg = 0 then a else
  let ni : Nat := r.n * 2 ^ k
  if ni = X then
    if 0 < r.sg then { a with cle := a.cle + 1, apl := a.apl + r.clo, aph := a.aph + r.chi }
    else { a with cle := a.cle + 1, anl := a.anl + r.clo, anh := a.anh + r.chi }
  else
    let ad : Nat := if X ≤ ni then ni - X else X - ni
    let L := logT tab l2 ad 1
    let u := imul (r.clo, r.chi) (yEncl ad L LD)
    let g := imul (r.clo, r.chi) (L.1 - LD.2, L.2 - LD.1)
    let kt : Int := if r.sg < 0 then cdiv (2 * (-r.clo) * DD) (ad * ad) else 0
    if ni < X then
      { a with s := (a.s.1 + u.1, a.s.2 + u.2), g0 := a.g0 + g.1, kl := a.kl + kt, cl := a.cl + 1, cle := a.cle + 1 }
    else
      { a with s := (a.s.1 + u.1, a.s.2 + u.2), g0 := a.g0 + g.1, kr := a.kr + kt }

def epZero : EAcc := ⟨(0, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Node data at `x = X / (10^12 2^k)`. -/
def epData (c : Ctx) (k X : Nat) : EPt :=
  let D : Nat := DEC * 2 ^ k
  let a := c.rs.foldl (epStep c.tab c.l2 k X ((D * D : Nat) : Int) (logT c.tab c.l2 D 1)) epZero
  ⟨uHi a.s D, a.g0, a.kl, a.kr, a.cl, a.cle, a.apl, a.aph, a.anl, a.anh⟩

/-- Node data at `X / (10^12 2^k)`, computed at the reduced scale. -/
def epAt (c : Ctx) (X k : Nat) : EPt := epData c (canon X k).2 (canon X k).1

/-- Upper bound (scale `2^(P+QS)`) of `2 |C| log h` for nodes with `C < 0` (sums `nl ≤ 2^QS C ≤ nh`), `lhi ≥ 2^P log h`. -/
def eTerm (nl nh lhi : Int) : Int := 2 * (if 0 ≤ lhi then (-nl) * lhi else (-nh) * lhi)

/-- Lower bounds `(L(p), L(q))` of a chord leaf from the node data `A` at `p` and `B` at `q`, or `none`. The part after the
node data is that of `chordLB`. -/
def chordLBC (c : Ctx) (A B : EPt) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) : Option (Int × Int) :=
  let D : Nat := DEC * 2 ^ k
  let H : Nat := Xq - Xp
  if Xp < Xq ∧ H ≤ D ∧ B.cl = A.cle then
    let LD := logT c.tab c.l2 D 1
    let Lh := logT c.tab c.l2 H 1
    let lh : Int × Int := (Lh.1 - LD.2, Lh.2 - LD.1)
    let Yh := yEncl H Lh LD
    let uP : Int := A.uhi - fdiv (imul (B.apl, B.aph) Yh).1 (D * D * 2 ^ (QS + 2))
    let uQ : Int := B.uhi - fdiv (imul (A.apl, A.aph) Yh).1 (D * D * 2 ^ (QS + 2))
    let gp : Int := A.g0 - (imul (B.apl + B.anl, B.aph + B.anh) lh).2
    let gq : Int := B.g0 - (imul (A.apl + A.anl, A.aph + A.anh) lh).2
    let m : Int := eTerm A.anl A.anh lh.2 + eTerm B.anl B.anh lh.2 + max (-2 * gp) (-2 * gq) +
      cdiv ((A.kl + B.kr) * ((H * H : Nat) : Int) * 2 ^ P) (8 * D * D)
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
      let Ap := mainLo Xp D + base + pap - 2 * uP
      let Aq := mainLo Xq D + base + paq - 2 * uQ
      let mn : Int := if 0 < m then cdiv (m * (H : Int) * (H : Int)) (D * D * 2 ^ QS) else 0
      let corr : Int := cdiv (mn + mp) 8
      if x0q then some (Ap + t0 + sl - corr, Aq + t0 - corr)
      else some (Ap + t0 - corr, Aq + t0 + sl - corr)
  else none

def chordOKC (c : Ctx) (A B : EPt) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) : Bool :=
  match chordLBC c A B Xp Xq k x0q mask with
  | some (lp, lq) => decide (0 < lp) && decide (0 < lq)
  | none => false

def leafOKE (c : Ctx) (l : Leaf) : Bool :=
  if l.kind = 0 then chordOKC c (epAt c l.X1 l.k) (epAt c l.X2 l.k) l.X1 l.X2 l.k l.x0q l.mask
  else windowOK c l.X1 l.X2 l.k

/-- The leaves tile `[X0 / D0, XT / DT]` in order and each passes (`leavesOK` with `leafOKE`). -/
def leavesOKE (c : Ctx) : Nat → Nat → List Leaf → Nat → Nat → Bool
  | X, kx, [], XT, kT => ptEq X kx XT kT
  | X, kx, l :: ls, XT, kT => ptEq X kx l.X1 l.k && leafOKE c l && leavesOKE c l.X2 l.k ls XT kT

/-! ## Benchmark variant on recursor-level integer primitives (after the companion KernelArith v2 primitives) -/

noncomputable section

def isnnK (m n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat (Nat.sub m n)) (fun k _ => Int.negSucc k) (Nat.sub n m)
def iaddK (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.add m n)) (fun n => isnnK m (Nat.succ n)) b)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => isnnK n (Nat.succ m))
      (fun n => Int.negSucc (Nat.succ (Nat.add m n))) b) a
def nnegK (n : Nat) : Int := Nat.rec (motive := fun _ => Int) (Int.ofNat 0) (fun k _ => Int.negSucc k) n
def inegK (a : Int) : Int := Int.rec (motive := fun _ => Int) (fun m => nnegK m) (fun m => Int.ofNat (Nat.succ m)) a
def isubK (a b : Int) : Int := iaddK a (inegK b)
def imulK (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => Int.ofNat (Nat.mul m n)) (fun n => nnegK (Nat.mul m (Nat.succ n))) b)
    (fun m => Int.rec (motive := fun _ => Int) (fun n => nnegK (Nat.mul (Nat.succ m) n))
      (fun n => Int.ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) b) a
def bleK (a b : Int) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Int.rec (motive := fun _ => Bool) (fun n => Nat.ble m n) (fun _ => false) b)
    (fun m => Int.rec (motive := fun _ => Bool) (fun _ => true) (fun n => Nat.ble n m) b) a
def bselK {α : Type} (c : Bool) (t e : α) : α := Bool.rec (motive := fun _ => α) e t c
def minK (a b : Int) : Int := bselK (bleK a b) a b
def maxK (a b : Int) : Int := bselK (bleK a b) b a
def zeroK (a : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun m => Nat.beq m 0) (fun _ => false) a
def posK (a : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun m => Nat.ble 1 m) (fun _ => false) a
def negK (a : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => true) a
/-- `⌊a / b⌋` (`Int.ediv a b`). -/
def fdivK (a : Int) (b : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Nat.div m b))
    (fun m => Nat.rec (motive := fun _ => Int) (Int.ofNat 0) (fun b' _ => Int.negSucc (Nat.div m (Nat.succ b'))) b) a
def cdivK (a : Int) (b : Nat) : Int := inegK (fdivK (inegK a) b)
def imulIK (a b : Int × Int) : Int × Int :=
  let p1 := imulK a.1 b.1
  let p2 := imulK a.1 b.2
  let p3 := imulK a.2 b.1
  let p4 := imulK a.2 b.2
  (minK (minK p1 p2) (minK p3 p4), maxK (maxK p1 p2) (maxK p3 p4))

def epStepKA (tab : Nat) (l2 : Nat × Nat) (k X : Nat) (DD : Int) (LD : Int × Int) (c3 : Int) (a : EAcc) (r : NRec) :
    EAcc :=
  bselK (zeroK r.sg) a <|
  let ni : Nat := Nat.mul r.n (Nat.pow 2 k)
  bselK (Nat.beq ni X)
    (bselK (posK r.sg)
      { a with cle := Nat.succ a.cle, apl := iaddK a.apl r.clo, aph := iaddK a.aph r.chi }
      { a with cle := Nat.succ a.cle, anl := iaddK a.anl r.clo, anh := iaddK a.anh r.chi }) <|
  let ad : Nat := bselK (Nat.ble X ni) (Nat.sub ni X) (Nat.sub X ni)
  let L := logT tab l2 ad 1
  let a2 : Int := Int.ofNat (Nat.mul ad ad)
  let v1 := isubK L.1 LD.2
  let v2 := isubK L.2 LD.1
  let u := imulIK (r.clo, r.chi) (imulK a2 (isubK (imulK 2 v1) c3), imulK a2 (isubK (imulK 2 v2) c3))
  let g := imulIK (r.clo, r.chi) (v1, v2)
  let kt : Int := bselK (negK r.sg) (cdivK (imulK (imulK 2 (inegK r.clo)) DD) (Nat.mul ad ad)) 0
  bselK (Nat.blt ni X)
    { a with s := (iaddK a.s.1 u.1, iaddK a.s.2 u.2), g0 := iaddK a.g0 g.1, kl := iaddK a.kl kt, cl := Nat.succ a.cl,
             cle := Nat.succ a.cle }
    { a with s := (iaddK a.s.1 u.1, iaddK a.s.2 u.2), g0 := iaddK a.g0 g.1, kr := iaddK a.kr kt }

def epDataKA (c : Ctx) (k X : Nat) : EPt :=
  let D : Nat := DEC * 2 ^ k
  let a := c.rs.foldl (epStepKA c.tab c.l2 k X ((D * D : Nat) : Int) (logT c.tab c.l2 D 1) (3 * 2 ^ P)) epZero
  ⟨uHi a.s D, a.g0, a.kl, a.kr, a.cl, a.cle, a.apl, a.aph, a.anl, a.anh⟩

end

/-! ## The benchmark variant computes `epData` -/

theorem isnnK_eq (m n : Nat) : isnnK m n = Int.subNatNat m n := by
  show Nat.rec (motive := fun _ => Int) (Int.ofNat (m - n)) (fun k _ => Int.negSucc k) (n - m) = Int.subNatNat m n
  unfold Int.subNatNat
  cases n - m <;> rfl

theorem iaddK_eq (a b : Int) : iaddK a b = a + b := by
  cases a <;> cases b <;> simp only [iaddK, isnnK_eq] <;> rfl

theorem nnegK_eq (n : Nat) : nnegK n = -(n : Int) := by
  cases n <;> rfl

theorem inegK_eq (a : Int) : inegK a = -a := by
  cases a with
  | ofNat n => simp only [inegK, nnegK_eq]; rfl
  | negSucc n => rfl

theorem isubK_eq (a b : Int) : isubK a b = a - b := by
  simp only [isubK, iaddK_eq, inegK_eq, Int.sub_eq_add_neg]

theorem imulK_eq (a b : Int) : imulK a b = a * b := by
  cases a <;> cases b <;> simp only [imulK, nnegK_eq] <;> rfl

theorem bleK_iff (a b : Int) : bleK a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp only [bleK, Nat.ble_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Bool.false_eq_true,
    false_iff, true_iff] <;> first | omega | (constructor <;> intro <;> omega)

theorem bleK_eq (a b : Int) : bleK a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, bleK_iff, decide_eq_true_iff]

theorem bselK_eq {α : Type} (c : Bool) (t e : α) : bselK c t e = if c = true then t else e := by
  cases c <;> rfl

theorem minK_eq (a b : Int) : minK a b = min a b := by
  simp only [minK, bselK_eq, bleK_eq, decide_eq_true_eq, Int.min_def]

theorem maxK_eq (a b : Int) : maxK a b = max a b := by
  simp only [maxK, bselK_eq, bleK_eq, decide_eq_true_eq, Int.max_def]

theorem zeroK_eq (a : Int) : zeroK a = decide (a = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases a <;> simp only [zeroK, Nat.beq_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Bool.false_eq_true, false_iff]
    <;> first | omega | (constructor <;> intro <;> omega)

theorem posK_eq (a : Int) : posK a = decide (0 < a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases a <;> simp only [posK, Nat.ble_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Bool.false_eq_true, false_iff]
    <;> first | omega | (constructor <;> intro <;> omega)

theorem negK_eq (a : Int) : negK a = decide (a < 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases a <;> simp only [negK, Int.ofNat_eq_natCast, Int.negSucc_eq, Bool.false_eq_true, false_iff, true_iff]
    <;> first | omega | (constructor <;> intro <;> omega)

theorem fdivK_eq (a : Int) (b : Nat) : fdivK a b = fdiv a b := by
  cases a <;> cases b <;> rfl

theorem cdivK_eq (a : Int) (b : Nat) : cdivK a b = cdiv a b := by
  simp only [cdivK, cdiv, inegK_eq, fdivK_eq, fdiv]
  rfl

theorem imulIK_eq (a b : Int × Int) : imulIK a b = imul a b := by
  simp only [imulIK, imul, imulK_eq, minK_eq, maxK_eq]

theorem epStepKA_eq (tab : Nat) (l2 : Nat × Nat) (k X : Nat) (DD : Int) (LD : Int × Int) (a : EAcc) (r : NRec) :
    epStepKA tab l2 k X DD LD (3 * 2 ^ P) a r = epStep tab l2 k X DD LD a r := by
  unfold epStepKA epStep yEncl
  simp only [bselK_eq, zeroK_eq, posK_eq, negK_eq, decide_eq_true_eq, iaddK_eq, imulK_eq, isubK_eq, inegK_eq,
    imulIK_eq, cdivK_eq, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq, Nat.succ_eq_add_one,
    Int.ofNat_eq_natCast]

theorem epDataKA_eq (c : Ctx) (k X : Nat) : epDataKA c k X = epData c k X := by
  unfold epDataKA epData
  have h : epStepKA c.tab c.l2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : Nat) : Int) (logT c.tab c.l2 (DEC * 2 ^ k) 1)
      (3 * 2 ^ P) = epStep c.tab c.l2 k X ((DEC * 2 ^ k * (DEC * 2 ^ k) : Nat) : Int) (logT c.tab c.l2 (DEC * 2 ^ k) 1) := by
    funext a r
    exact epStepKA_eq _ _ _ _ _ _ a r
  simp only [h]

/-! ## Composition (for the kernel track) -/

/-- A chord leaf passes if its end-point data are those of the reduced end points and `chordOKC` holds for them. -/
theorem leafOKE_of_parts {c : Ctx} {X1 X2 k : Nat} {x0q : Bool} {mask Xa ka Xb kb : Nat} {A B : EPt}
    (ha : canon X1 k = (Xa, ka)) (hA : epDataKA c ka Xa = A) (hb : canon X2 k = (Xb, kb)) (hB : epDataKA c kb Xb = B)
    (h : chordOKC c A B X1 X2 k x0q mask = true) : leafOKE c ⟨0, X1, X2, k, x0q, mask⟩ = true := by
  rw [epDataKA_eq] at hA hB
  simp only [leafOKE, epAt, ha, hb, hA, hB, ite_true]
  exact h

theorem leavesOKE_cons {c : Ctx} {X kx XT kT : Nat} {l : Leaf} {ls : List Leaf} (h1 : ptEq X kx l.X1 l.k = true)
    (h2 : leafOKE c l = true) (h3 : leavesOKE c l.X2 l.k ls XT kT = true) : leavesOKE c X kx (l :: ls) XT kT = true := by
  simp only [leavesOKE, h1, h2, h3, Bool.and_self]

theorem leavesOKE_nil {c : Ctx} {X kx XT kT : Nat} (h : ptEq X kx XT kT = true) : leavesOKE c X kx [] XT kT = true := by
  simp only [leavesOKE, h]

end T86Core
