def csSb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then 16 else s0.regs i }
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 416), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre 4096 RW (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 csSb := by
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]; exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]; intro r hr; simp at hr; subst hr; simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, Outside, calleeStack]; decide
  · simp only [calleeStack, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · exact Or.inl ⟨rfl, zp, by decide⟩
  · exact s0_inv _ _ (by simp [HSIZE])
  · intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)

def csCv0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 zp else if i = 1 then 16 else s0.regs i }
def csCv : State := { csCv0 with sp := BitVec.ofNat 64 (sp0 - 32), pc := BitVec.ofNat 64 cvAddr }

set_option maxRecDepth 100000 in
theorem csCv_pre : RtLivePre 4096 RW (convTstringSpec) convTstringLive cvAddr [] 0x100000 csCv := by
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · trivial
  · intro r hr; simp [convTstringSpec] at hr
  · simp only [calleeStack, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · exact Or.inr ⟨rfl, zp, by decide⟩
  · exact s0_inv _ _ (by simp [HSIZE])
  · intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)
