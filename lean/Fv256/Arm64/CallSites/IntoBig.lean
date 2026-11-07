/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `PC` at the stub's entry and the argument registers of a request `ok` serves. -/
def csNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 bigType else s0.regs i }
def csNew : State := { csNew0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }
def csW1 : State := { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectPre 4096 csNew ∧ StackRoom csNew 4096 1 ∧
    LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(csNew.regs 0).toNat] [] 0x400 (newobjectRound csNew)
      (csNew.regs 28).toNat csNew.mem (calleeStack csNew 4096 1) := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), typeOK_of (by decide) (by decide), by decide⟩, ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl (by decide)⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csW1_pre : CallOK csW1 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.inv 0x400 [] (csW1.regs 28).toNat (view R.rt [] csW1.mem) ∧
    LiveSep [] [(csW1.sp.toNat - 4096, csW1.sp.toNat - 8)] ∧ LiveSep [(csW1.sp.toNat - 4096, csW1.sp.toNat - 8)] R.rt := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide

set_option maxRecDepth 100000 in
theorem csW2_pre : CallOK csW2 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv 0x400 [] (csW2.regs 28).toNat (view R.rt [] csW2.mem) ∧
    LiveSep [] [(csW2.sp.toNat - 4096, csW2.sp.toNat - 8)] ∧ LiveSep [(csW2.sp.toNat - 4096, csW2.sp.toNat - 8)] R.rt := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide
