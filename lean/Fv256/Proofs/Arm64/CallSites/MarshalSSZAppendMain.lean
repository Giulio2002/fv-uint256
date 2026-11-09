def csG0 : State := { s0 with regs := fun i => if i = 0 then dpV else if i = 1 then 40 else if i = 2 then 32 else if i = 3 then 8 else if i = 4 then BitVec.ofNat 64 u8A else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `SP = sp0 - 128`. -/
def csG : State := { csG0 with sp := BitVec.ofNat 64 (sp0 - 128), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, argWords, wordsFrom, arg]
    exact ⟨⟨typeOK_of (by decide) (by decide), by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [argWords, wordsFrom, arg, Outside, calleeStack]; decide)
  · rw [addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)
