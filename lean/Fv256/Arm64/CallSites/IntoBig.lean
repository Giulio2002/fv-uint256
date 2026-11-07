/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `PC` at the stub's entry and the argument registers of a request `ok` serves. -/
def csNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 bigType else s0.regs i }
def csNew : State := { csNew0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }
def csW1 : State := { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), typeOK_of (by decide) (by decide), by decide⟩, ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl (by decide)⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide
