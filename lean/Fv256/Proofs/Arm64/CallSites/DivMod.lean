def wsNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): at the allocator's entry, `X0 = Int`'s type descriptor, `SP` = the frame
of the caller (the argument of `H` in `hHW`), `X28`/memory as in `s0`. -/
def wsNew : State := { wsNew0 with sp := BitVec.ofNat 64 (sp0 - 160), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite HW rtW 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = intType := by
    have hpt : intType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 160 := by decide
  show HW [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rtW wsNew.mem)
  rw [e0, e1, e2]
  exact hHW
