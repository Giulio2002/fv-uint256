def csSb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 2 else s0.regs i }
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 432), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Hw (argWords csSb 3) (csSb.regs 28).toNat csSb.sp.toNat (rtView rtT csSb.mem)
    refine ⟨⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide⟩

def csSt0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 2 else s0.regs i }
def csSt : State := { csSt0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 stAddr }

set_option maxRecDepth 100000 in
theorem csSt_pre : RtPre rtT 4096 Hw stringtoslicebyteSpec csSt := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Hw (argWords csSt 3) (csSt.regs 28).toNat csSt.sp.toNat (rtView rtT csSt.mem)
    refine ⟨⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide⟩

