def csSb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 HEAP else if i = 2 then BitVec.ofNat 64 5 else s0.regs i }
/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `slicebytetostring(nil, HEAP, 5)` at its entry, in the caller's frame (`SP = sp0 - 400`). -/
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 400), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show H1 (argWords csSb 3) (csSb.regs 28).toNat csSb.sp.toNat (rtView rtW csSb.mem)
    refine ⟨by decide, by decide, ?_, by decide⟩
    decide
