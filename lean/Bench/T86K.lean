import T86Core.CheckE
open T86Core

def litI (x : Int) : String := if x < 0 then s!"({x})" else s!"{x}"

/-- Native helper for the K shards: `ctx` prints the context `mkCtx iLoNum 128` as a Lean literal (checked equal by
the kernel in `T86K.Lits`); `eblk i0 cnt` prints `iBlock i0 cnt`; `irow i a m` prints the piece `iRow` of row `i` over
the records `a .. a+m-1`, and `irows FILE` does so for each line `i a m` of FILE; `elits` prints the energy table and
records as Lean literals (checked equal by the kernel in `T86K.ELitsEq`). Its output is untrusted: the kernel checks
every value it supplied. The lower-bound kernel modules are not part of this release. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["ctx", iNumS, iShS] =>
    let c := mkCtx iNumS.toInt! iShS.toNat!
    let recs := ", ".intercalate (c.rs.map fun r => s!"⟨{r.n}, {litI r.sg}, {litI r.clo}, {litI r.chi}⟩")
    IO.println s!"def ctxLit : Ctx where\n  tab := {c.tab}\n  l2 := ({c.l2.1}, {c.l2.2})\n  rs := [{recs}]\n  m0hi := {litI c.m0hi}\n  isLo := {litI c.isLo}\n  sumC := {c.sumC}"
  | ["eblk", a, b] =>
    let t0 ← IO.monoNanosNow
    let v := iBlock a.toNat! b.toNat!
    let t1 ← IO.monoNanosNow
    IO.println s!"block {a} {b}: lo {v.1} hi {v.2} ({(t1 - t0) / 1000000} ms)"
  | ["eblks", path] =>
    let lines ← IO.FS.lines path
    let mut slo : Int := 0
    let mut shi : Int := 0
    for ln in lines do
      match (ln.splitOn " ").filter (· ≠ "") with
      | [a, b] =>
        let v := iBlock a.toNat! b.toNat!
        slo := slo + v.1
        shi := shi + v.2
        IO.println s!"block {a} {b}: lo {v.1} hi {v.2}"
      | _ => pure ()
    IO.println s!"sum: lo {slo} hi {shi}"
  | ["irow", i, a, m] =>
    let r := recsI.getD i.toNat! ⟨0, 0, 0, 0⟩
    let t0 ← IO.monoNanosNow
    let v := iRow TABI L2I (logI TABI L2I DEC 1) r ((recsI.drop a.toNat!).take m.toNat!)
    let t1 ← IO.monoNanosNow
    IO.println s!"irow {i} {a} {m}: lo {litI v.1} hi {litI v.2} sg {r.sg} ({(t1 - t0) / 1000000} ms)"
  | ["irows", path] =>
    let lines ← IO.FS.lines path
    for ln in lines do
      match (ln.splitOn " ").filter (· ≠ "") with
      | [i, a, m] =>
        let r := recsI.getD i.toNat! ⟨0, 0, 0, 0⟩
        let v := iRow TABI L2I (logI TABI L2I DEC 1) r ((recsI.drop a.toNat!).take m.toNat!)
        IO.println s!"{i} {a} {m} {v.1}"
      | _ => pure ()
  | ["elits"] =>
    let lD := logI TABI L2I DEC 1
    let recs := ",\n  ".intercalate (recsI.map fun r => s!"⟨{r.n}, {litI r.sg}, {litI r.clo}, {litI r.chi}⟩")
    IO.println s!"def tabILit : Nat := {TABI}\n\ndef l2ILit : Nat × Nat := ({L2I.1}, {L2I.2})\n\ndef lDecLit : Int × Int := ({litI lD.1}, {litI lD.2})\n\ndef recsILit : List NRec := [\n  {recs}]"
  | ["eps", iNumS, iShS, path] =>
    -- end-point data `epData` for each line `X k` of FILE (k already reduced by `canon`), as Lean literals
    let c := mkCtx iNumS.toInt! iShS.toNat!
    let lines ← IO.FS.lines path
    for ln in lines do
      match (ln.splitOn " ").filter (· ≠ "") with
      | [x, k] =>
        let e := epData c k.toNat! x.toNat!
        IO.println s!"{x} {k} ⟨{litI e.uhi}, {litI e.g0}, {litI e.kl}, {litI e.kr}, {e.cl}, {e.cle}, {litI e.apl}, {litI e.aph}, {litI e.anl}, {litI e.anh}⟩"
      | _ => pure ()
  | _ => IO.println "usage: t86k ctx INUM ISH | t86k eblk I0 CNT | t86k eblks FILE | t86k irow I A M | t86k irows FILE | t86k elits | t86k eps INUM ISH FILE"
