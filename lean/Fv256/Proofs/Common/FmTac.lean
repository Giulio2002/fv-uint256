import Lean
open Lean Elab Tactic Meta

/-- `fm_clear_ddisj k₁ k₂ ..`: clear the `h_ddisj<i>_<k>` facts that `janus_data` adds (one disjunction per writable range `i` and data
object `k`) except those for the data objects `k₁ k₂ ..` that the proof reads.  Format's extraction has many more data objects than the
single-function extractions, and `omega` case-splits every disjunction in the context. -/
elab "fm_clear_ddisj " ks:num* : tactic => withMainContext do
  let keep := ks.toList.map (·.getNat)
  let mut g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let n := d.userName.toString
    if n.startsWith "h_ddisj" then
      match (n.splitOn "_").getLast? >>= String.toNat? with
      | some k => if !(keep.contains k) then g ← g.clear d.fvarId
      | none => pure ()
  replaceMainGoal [g]
