def csMk0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 1 then 5#64 else if i = 2 then 5#64 else s0.regs i }
/-- The call state of `runtime.makeslice` (U-WITNESS-CALLSITE): `makeslice(uint8, 5, 5)` at its entry in the caller's frame (`SP = sp0 - 48`, as in `hH`). -/
def csMk : State := { csMk0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") }

set_option maxRecDepth 100000 in
theorem csMk_pre : MakesliceSite H rt 4096 csMk := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide, by decide, by decide⟩, ?_⟩
  have e0 : (csMk.regs 0).toNat = byteType := by
    have hpt : byteType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (csMk.regs 1).toNat = 5 := by decide
  have e2 : (csMk.regs 2).toNat = 5 := by decide
  have e3 : (csMk.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e4 : csMk.sp.toNat = s0.sp.toNat - 48 := by decide
  show H [(csMk.regs 0).toNat, (csMk.regs 1).toNat, (csMk.regs 2).toNat] (csMk.regs 28).toNat csMk.sp.toNat (rtView rt csMk.mem)
  rw [e0, e1, e2, e3, e4]
  exact hH
