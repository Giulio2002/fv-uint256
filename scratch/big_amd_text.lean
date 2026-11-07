
/-! ### The large-value path (`z = 10^7`: eight digits, `FormatUint` path, both runtime calls made) -/

open Fv256.ToyRuntime64 in
def Hw8 : RtReady := fun a _ sp view =>
  (∃ p, a = [0, p, 8]) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true ∧
    (sp + 8 ≤ hA ∨ hA + 8 ≤ sp) ∧ (sp + 8 ≤ hB ∨ hB + 8 ≤ sp)

open Fv256.ToyRuntime64 in
def implAt8 : List Amd64.Segment :=
  [{ name := "model-sbts", base := ssAddr, bytes := sbts8Code hA }, { name := "model-stb", base := stAddr, bytes := stb8Code hB }]
def linked8 : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt8 }
theorem linked_eq8 : Extracted.program.link implAt8 = linked8 := rfl

theorem copy8_bytes (m : Janus.Arm64.Memory) (a p : Nat) :
    Spec.strBytes (m.writeLE a 8 (m.readLE p 8)) a 8 = Spec.strBytes m p 8 := by
  apply Janus.Spec.strBytes_congr
  intro i hi
  have := Janus.Contracts.IfaceModel.bytes_writeLE_readLE m a p 8 i hi
  exact this

theorem model1_8 : RtContract64 (Extracted.program.link implAt8) ssAddr rtT 4096 Hw8
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw8, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8, hdA, hdB⟩ := ha
  have hargs : argWords64 s 3 = [0, p, 8] := hp
  simp [slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8 hdA hdB
  obtain ⟨h0, h3, h1⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 3).toNat 8 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h3, copy8_bytes]
    refine ⟨⟨trivial, ?_, rfl⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · right; right; right
      exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩

theorem model2_8 : RtContract64 (Extracted.program.link implAt8) stAddr rtT 4096 Hw8 stringtoslicebyteSpec := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw8, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  have hargs : argWords64 s 3 = [0, p, 8] := hp
  simp [stringtoslicebyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs] at hp hstr hbuf hdis
  obtain ⟨h0, h3, h1⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 3).toNat 8 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h3]
    have hr : roundupsize 8 true = 8 := by decide
    refine ⟨by simp [Spec.strBytes], fun h => absurd rfl h, fun _ => ⟨by simp [Spec.strBytes, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · rw [copy8_bytes]
    · intro i hi
      omega

def bytes8 (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = zp then 0x80 else if a = zp + 1 then 0x96 else if a = zp + 2 then 0x98 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def s08 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes8, [⟨sp0 - 4608, 4608 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 8, true⟩] ++ dregs⟩ }

theorem hret8 : RetAddr linked8 ret := RetAddr.of_check (by decide)

theorem setup8 : CallSetup (linked8.withExit ret) Extracted.entry [arg] s08 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded8 : Extracted.program.DataLoaded s08.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem hz8 : s08.mem.readLE arg.toNat 32 = 10000000 := by
  unfold s08 arg zp
  decide

theorem hdl8 : decLen 10000000 = 8 := by
  simp (disch := omega) [decLen_ge, decLen_lt]

set_option maxRecDepth 100000 in
theorem pre8 : StackGuardOK s08 (0x378 + 40) ∧ StackWritable s08 4608 8 ∧ Extracted.program.DataLoaded s08.mem ∧
    Outside ((s08.regs 4).toNat - 4608) (4608 + 8) rtT ∧ Outside 5163273 256 rtT ∧ Outside 5176582 256 rtT ∧
    (∀ r ∈ rtT, 32 ≤ r.1) ∧
    (s08.regs 4).toNat % 8 = 0 ∧ Buffer s08 arg 32 false ∧
    (arg.toNat + 32 ≤ (s08.regs 4).toNat - 4608 ∨ (s08.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s08.regs 14).toNat + 24 ≤ (s08.regs 4).toNat - 4608 ∨ (s08.regs 4).toNat + 8 ≤ (s08.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s08.mem.readLE arg.toNat 32 →
      Hw8 [0, (s08.regs 4).toNat - 40 - 0x178 + 86 + (98 - decLen (s08.mem.readLE arg.toNat 32)), decLen (s08.mem.readLE arg.toNat 32)]
        (s08.regs 14).toNat ((s08.regs 4).toNat - 40 - 0x178 - 8) (rtView rtT s08.mem)) ∧
    (100 ≤ s08.mem.readLE arg.toNat 32 → s08.mem.readLE arg.toNat 32 < 2 ^ 64 →
      Hw8 [0, (s08.regs 4).toNat - 40 - 384 - 0x20 + (24 - decLen (s08.mem.readLE arg.toNat 32)), decLen (s08.mem.readLE arg.toNat 32)]
        (s08.regs 14).toNat ((s08.regs 4).toNat - 40 - 384 - 0x58) (rtView rtT s08.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s08.mem M (rtT ++ [((s08.regs 4).toNat - 4608, (s08.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s08.mem.readLE arg.toNat 32)) →
      DecAt rtT 5163273 5176582 5134938 p l →
      Hw8 [0, p, l] (s08.regs 14).toNat ((s08.regs 4).toNat - 40) (rtView rtT M)) := by
  rw [hz8, hdl8]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded8, ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => absurd h (by decide), fun _ _ => ⟨⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB]; decide
  · rw [rtView_acc]; decide
  · rw [rtView_acc]; decide
  · simp only [s08, sp0, hA]; decide
  · simp only [s08, sp0, hB]; decide
  · intro M p l hMF hSO hDA
    have hl : l = 8 := by
      have h := hSO.1
      have h8 : (decBytes 10000000).length = 8 := hdl8
      omega
    subst hl
    refine ⟨⟨p, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [rtView_acc, hMF.accessible]; decide
    · rw [rtView_acc, hMF.accessible]; decide
    · simp only [s08, sp0, hA]; decide
    · simp only [s08, sp0, hB]; decide

/-- **Large-value witness**: `z = 10^7` (eight digits, `FormatUint` path): both runtime calls are made and the readiness hypothesis for the
second call is exercised on the string `Dec` returns. -/
theorem big : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s (0x378 + 40) ∧ StackWritable s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4608) (4608 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
    (∀ r ∈ rt, 32 ≤ r.1) ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4608 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4608 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      H [0, (s.regs 4).toNat - 40 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 40 - 0x178 - 8) (rtView rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (s.regs 4).toNat - 40 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 40 - 384 - 0x58) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l →
      H [0, p, l] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt M))) ∧
    100 ≤ s.mem.readLE z.toNat 32 :=
  ⟨implAt8, rtT, Hw8, ret, s08, arg, model1_8, model2_8, by rw [linked_eq8]; exact hret8, by rw [linked_eq8]; exact setup8, pre8,
    by rw [hz8]; decide⟩
