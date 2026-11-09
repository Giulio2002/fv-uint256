/-- The call state of `runtime.convT64` (U-WITNESS-CALLSITE): `convT64(len)` at its entry, `SP = sp0 - 112`, memory of `s0`. -/
def csCv0 : State := { s0 with regs := fun i => if i = 0 then 5 else s0.regs i }
def csCv : State := { csCv0 with sp := BitVec.ofNat 64 (sp0 - 112), pc := BitVec.ofNat 64 cAddrC }

set_option maxRecDepth 100000 in
theorem csCv_pre : ConvT64Site R0 Htrue csCv := by
  refine ⟨⟨⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, by decide⟩,
    callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩, trivial⟩
  · unfold Desc; decide
  · simp only [R0_priv, R0_depth, outside_cons, outside_nil, and_true]; decide

/-- The memory of the `fmt.errorf` call: the `[]any` `{{*errorString, ErrBad..}, {int, &len}, {int, &32}}` at `sp0 - 56` and the box of `len` at `BOX`. -/
def mE1 : Memory := mem0.writeLE (sp0 - 56) 8 tErr
def mE2 : Memory := mE1.writeLE (sp0 - 48) 8 evData
def mE3 : Memory := mE2.writeLE (sp0 - 40) 8 tInt
def mE4 : Memory := mE3.writeLE (sp0 - 32) 8 BOX
def mE5 : Memory := mE4.writeLE (sp0 - 24) 8 tInt
def mE6 : Memory := mE5.writeLE (sp0 - 16) 8 c32Addr
def memE : Memory := mE6.writeLE BOX 8 5
def csEr0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 fmtAddr else if i = 1 then 26 else if i = 2 then BitVec.ofNat 64 (sp0 - 56)
    else if i = 3 then 3 else if i = 4 then 3 else s0.regs i, mem := memE }
/-- The call state of `fmt.errorf` (U-WITNESS-CALLSITE): `Errorf(fmt, []any{err, len, 32})` at its entry, `SP = sp0 - 112`. -/
def csEr : State := { csEr0 with sp := BitVec.ofNat 64 (sp0 - 112), pc := BitVec.ofNat 64 cAddrE }

abbrev rsE : List (Nat × Nat) := [(sp0 - 4208, sp0 + 24), (BOX, BOX + 8)]
theorem rsE1 : (sp0 - 4208, sp0 + 24) ∈ rsE := by simp [rsE]
theorem rsE2 : (BOX, BOX + 8) ∈ rsE := by simp [rsE]
theorem fE1 : MemFrame mem0 mE1 rsE := (MemFrame.refl mem0 rsE).writeLE (a := sp0 - 56) (k := 8) tErr rsE1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)
theorem fE2 : MemFrame mem0 mE2 rsE := fE1.writeLE (a := sp0 - 48) (k := 8) evData rsE1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)
theorem fE3 : MemFrame mem0 mE3 rsE := fE2.writeLE (a := sp0 - 40) (k := 8) tInt rsE1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)
theorem fE4 : MemFrame mem0 mE4 rsE := fE3.writeLE (a := sp0 - 32) (k := 8) BOX rsE1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)
theorem fE5 : MemFrame mem0 mE5 rsE := fE4.writeLE (a := sp0 - 24) (k := 8) tInt rsE1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)
theorem fE6 : MemFrame mem0 mE6 rsE := fE5.writeLE (a := sp0 - 16) (k := 8) c32Addr rsE1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)
theorem csEr_frame : MemFrame mem0 memE rsE := fE6.writeLE (a := BOX) (k := 8) 5 rsE2 (by simp only [BOX]; omega) (by simp only [BOX]; omega)

theorem csEr_view : view R0e.rt [] memE = view R0e.rt [] mem0 := by
  have hrt : R0e.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  have hO1 : Outside (sp0 - 4208) 4232 R0e.rt := by
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  have hO2 : Outside BOX 8 R0e.rt := by
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, BOX, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  rw [view_nil, view_nil]
  refine Janus.Contracts.Stack.rtView_eq_of_frame csEr_frame rfl (fun a ha => ?_)
  have d1 := InRanges.disjoint ha hO1
  have d2 := InRanges.disjoint ha hO2
  simp only [rsE, outside_cons, outside_nil]
  refine ⟨?_, ?_, trivial⟩ <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem csEr_pre : ErrorfLiveSite R0e cAddrE 4096 tErr iErr tInt iWrap 26 fmtNum 4294967296 [] 138 csEr := by
  have hrt : R0e.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  have hrd : Janus.Contracts.Errorf.errorfReads csEr.mem (csEr.regs 0).toNat (csEr.regs 1).toNat (csEr.regs 2).toNat =
      [(fmtAddr, 26), (sp0 - 56, 48), (evData, 16), (textAddr, 21), (BOX, 8), (c32Addr, 8)] := by decide
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩, ?_, ?_, ?_,
    ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · unfold Janus.Contracts.Errorf.ArgsOK; simp only [Readable]; decide
  · unfold ReadsOutside; rw [hrd]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [calleeStack, outside_cons, outside_nil]; decide)
  · unfold Janus.Contracts.Errorf.ReadsSafe; rw [hrd]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (Or.inl (by rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide))
  · trivial
  · show R0e.inv 138 [] (csEr.regs 28).toNat (view R0e.rt [] memE)
    rw [csEr_view]; exact rinv0 _
  · intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide)
