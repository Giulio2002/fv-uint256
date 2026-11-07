def csSb08 : State := { s08 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 8 else s08.regs i }
def csSb8 : State := { csSb08 with sp := BitVec.ofNat 64 (sp0 - 432), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb8_pre : RtPre rtT 4096 Hw8 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb8 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Hw8 (argWords csSb8 3) (csSb8.regs 28).toNat csSb8.sp.toNat (rtView rtT csSb8.mem)
    refine ⟨Or.inl ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide⟩

def csSt08 : State := { s08 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 8 else s08.regs i }
def csSt8 : State := { csSt08 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 stAddr }

set_option maxRecDepth 100000 in
theorem csSt8_pre : RtPre rtT 4096 Hw8 stringtoslicebyteSpec csSt8 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Hw8 (argWords csSt8 3) (csSt8.regs 28).toNat csSt8.sp.toNat (rtView rtT csSt8.mem)
    refine ⟨⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide⟩

