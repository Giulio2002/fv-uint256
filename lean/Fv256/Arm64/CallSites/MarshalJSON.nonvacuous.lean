def csSb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 2 else s0.regs i }
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 464), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Hw (argWords csSb 3) (csSb.regs 28).toNat csSb.sp.toNat (rtView rtT csSb.mem)
    refine ⟨Or.inl ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide⟩

def csCb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then 1007400 else if i = 2 then 1 else if i = 3 then BitVec.ofNat 64 zp else if i = 4 then BitVec.ofNat 64 2 else if i = 5 then 1007400 else if i = 6 then 1 else s0.regs i }
def csCb : State := { csCb0 with sp := BitVec.ofNat 64 (sp0 - 80), pc := BitVec.ofNat 64 cbAddr }

set_option maxRecDepth 100000 in
theorem csCb_pre : RtPre rtT 4096 Hw (concatbyteSpec 3) csCb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · refine ⟨Or.inl (by decide), strsIn_of (fun x hx => ?_) (by decide)⟩
    simp only [strPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨by decide, fun _ => by decide⟩
  · intro r hr
    simp only [concatbyteSpec, strPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (simp only [Outside, calleeStack]; decide)
  · show Hw (argWords csCb 7) (csCb.regs 28).toNat csCb.sp.toNat (rtView rtT csCb.mem)
    refine ⟨Or.inr ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide⟩

