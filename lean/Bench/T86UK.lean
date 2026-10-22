import T86UCore.Check
open T86UCore

def litI (x : Int) : String := if x < 0 then s!"({x})" else s!"{x}"

/-- Native helper for the upper K shards: prints the context `mkCtx` as a Lean literal (checked equal by the kernel in
`T86UK.Lits`). The kernel-track modules are not part of this release. -/
def main (_args : List String) : IO Unit := do
  let c := mkCtx
  let recs := ", ".intercalate (c.rs.map fun r => s!"⟨{r.n}, {litI r.sg}, {litI r.clo}, {litI r.chi}⟩")
  IO.println s!"def ctxULit : Ctx where\n  tab := {c.tab}\n  l2 := ({c.l2.1}, {c.l2.2})\n  rs := [{recs}]\n  m0hi := {litI c.m0hi}\n  isLo := {litI c.isLo}\n  sumC := {c.sumC}"
