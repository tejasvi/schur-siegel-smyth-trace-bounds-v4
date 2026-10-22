import T86UCore.Leaves
open T86UCore

/-- Native driver for the 86a upper checker: global checks, then the leaves of a text file
("C Xp Xq k x0q mask" / "W Xu Xv k" per line). -/
def main (args : List String) : IO Unit := do
  let path := args.headD "leaves_ub.txt"
  let t0 ← IO.monoNanosNow
  let c := mkCtx
  IO.println s!"dataOK {dataOK}; budgetOK {budgetOK}; traceOK {traceOK}; isLo {c.isLo}; sumC {c.sumC}; recs {c.rs.length}"
  IO.println s!"momentsOK {momentsOK c mom}; irredsOK {irredsOK mom}; leftTailPre {leftTailPre XLO 0} leftTail {leftTailLB c XLO 0}"
  let lines ← IO.FS.lines path
  let mut nok := 0
  let mut nbad := 0
  let mut minlb : Int := 1000000000000000000000000
  for ln in lines do
    let w := (ln.splitOn " ").filter (· ≠ "")
    match w with
    | ["C", a, b, k, x, m] =>
      match chordLB c a.toNat! b.toNat! k.toNat! (x == "1") m.toNat! with
      | some (lp, lq) =>
        if 0 < lp ∧ 0 < lq then
          nok := nok + 1
          minlb := min minlb (min lp lq)
        else
          nbad := nbad + 1
          IO.println s!"BAD {ln} {lp} {lq}"
      | none =>
        nbad := nbad + 1
        IO.println s!"NONE {ln}"
    | ["W", a, b, k] =>
      if windowOK c a.toNat! b.toNat! k.toNat! then
        nok := nok + 1
        minlb := min minlb (windowLB c a.toNat! b.toNat! k.toNat!)
      else
        nbad := nbad + 1
        IO.println s!"BADW {ln} {windowLB c a.toNat! b.toNat! k.toNat!}"
    | _ => pure ()
  let t1 ← IO.monoNanosNow
  IO.println s!"ok {nok} bad {nbad} minlb {minlb} ({(t1 - t0) / 1000000} ms)"
  IO.println s!"leavesOK {leavesOK c XLO 0 leaves XHI 0}"
