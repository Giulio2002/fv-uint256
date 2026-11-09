def csSb08 : State := { s08 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 8 else s08.regs i }
def csSb8 : State := { csSb08 with sp := BitVec.ofNat 64 (sp0 - 464), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb8_pre : RtPre rtT16 4096 Hw8 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb8 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Hw8 (argWords csSb8 3) (csSb8.regs 28).toNat csSb8.sp.toNat (rtView rtT16 csSb8.mem)
    refine ⟨Or.inl ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc16]; decide, by rw [rtView_acc16]; decide⟩

def csCb08 : State := { s08 with regs := fun i => if i = 0 then 0 else if i = 1 then 1007400 else if i = 2 then 1 else if i = 3 then BitVec.ofNat 64 zp else if i = 4 then BitVec.ofNat 64 8 else if i = 5 then 1007400 else if i = 6 then 1 else s08.regs i }
def csCb8 : State := { csCb08 with sp := BitVec.ofNat 64 (sp0 - 80), pc := BitVec.ofNat 64 cbAddr }

set_option maxRecDepth 100000 in
theorem csCb8_pre : RtPre rtT16 4096 Hw8 (concatbyteSpec 3) csCb8 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · refine ⟨Or.inl (by decide), strsIn_of (fun x hx => ?_) (by decide)⟩
    simp only [strPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨by decide, fun _ => by decide⟩
  · intro r hr
    simp only [concatbyteSpec, strPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (simp only [Outside, calleeStack]; decide)
  · show Hw8 (argWords csCb8 7) (csCb8.regs 28).toNat csCb8.sp.toNat (rtView rtT16 csCb8.mem)
    refine ⟨Or.inr ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc16]; decide, by rw [rtView_acc16]; decide⟩

