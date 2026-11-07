/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): at the allocator's entry, `X0 = Int`'s type descriptor, `SP` = NewInt's
frame (the argument of `H` in `hH`), `X28`/memory as in `s0`. -/
def wsNew : State :=
  { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject"), sp := BitVec.ofNat 64 (sp0 - 48),
    regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0 }

theorem wsNew_pre : NewobjectPre 4096 wsNew ∧ Ready H rt [(wsNew.regs 0).toNat] wsNew := by
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = intType := by
    have hpt : intType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 48 := by decide
  show H [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rt wsNew.mem)
  rw [e0, e1, e2]
  exact hH
