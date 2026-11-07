
/-! ### The large-value path (`z = 10^7`: eight digits, `FormatUint` path, both runtime calls made) -/

open Fv256.ToyRuntimeArm64 in
def Hw8 : RtReady := fun a _ _ view =>
  (∃ p, a = [0, p, 8]) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true

open Fv256.ToyRuntimeArm64 in
def implAt8 : List Segment :=
  [{ name := "model-sbts", base := ssAddr, words := sbts8Words }, { name := "model-stb", base := stAddr, words := stb8Words }]
def linked8 : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt8 }
theorem linked_eq8 : Extracted.program.link implAt8 = linked8 := rfl

theorem copy8_bytes (m : Janus.Arm64.Memory) (a p : Nat) :
    strBytes (m.writeLE a 8 (m.readLE p 8)) a 8 = strBytes m p 8 := by
  apply strBytes_congr
  intro i hi
  have := Janus.Contracts.IfaceModel.bytes_writeLE_readLE m a p 8 i hi
  exact this

theorem model1_8 : RtContract (Extracted.program.link implAt8) ssAddr rtT 4096 Hw8
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw8, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8⟩ := ha
  have hargs : argWords s 3 = [0, p, 8] := hp
  simp [slicebytetostringSpec, argWords, wordsFrom, arg] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8
  obtain ⟨h0, h1, h2⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 1).toNat 8 false = true := by
    have h := hs2 (by omega); rw [h2] at h; exact h
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h1, copy8_bytes]
    refine ⟨⟨trivial, ?_, rfl⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · right; right; right
      exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩

theorem model2_8 : RtContract (Extracted.program.link implAt8) stAddr rtT 4096 Hw8 stringtoslicebyteSpec := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw8, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8⟩ := ha
  have hargs : argWords s 3 = [0, p, 8] := hp
  simp [stringtoslicebyteSpec, argWords, wordsFrom] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8
  obtain ⟨h0, h1, h2⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 1).toNat 8 false = true := by
    have h := hs2 (by omega); rw [h2] at h; exact h
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h1]
    have hr : roundupsize 8 true = 8 := by decide
    refine ⟨by simp [strBytes], fun h => absurd rfl h, fun _ => ⟨by simp [strBytes, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · rw [copy8_bytes]
    · intro i hi
      omega

def bytes8 (a : Nat) : Byte :=
  if a = zp then 0x80 else if a = zp + 1 then 0x96 else if a = zp + 2 then 0x98 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def s08 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes8, [⟨sp0 - 4656, 4656 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 8, true⟩] ++ dregs⟩ }

theorem hret8 : RetAddr linked8 ret := RetAddr.of_check (by decide)

theorem setup8 : CallSetup (linked8.withExit ret) Extracted.entry [arg] s08 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s08] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded8 : Extracted.program.DataLoaded s08.mem := by
  unfold Program.DataLoaded
  decide +kernel

theorem hz8 : val256 s08.mem arg.toNat = 10000000 := by
  unfold val256 s08 arg zp
  decide

theorem hdl8 : decLen 10000000 = 8 := by
  simp (disch := omega) [decLen_ge, decLen_lt]

set_option maxRecDepth 100000 in
theorem pre8 : (GuardOK s08 (688 + 48) ∧ StackOK s08 4656 8 ∧ Extracted.program.DataLoaded s08.mem ∧
    Outside (s08.sp.toNat - 4656) (4656 + 8) rtT ∧ Outside 989280 256 rtT ∧ Outside 1002589 256 rtT ∧ (∀ r ∈ rtT, 32 ≤ r.1) ∧
    Ptr32 s08.mem arg false ∧ (arg.toNat + 32 ≤ s08.sp.toNat - 4656 ∨ s08.sp.toNat + 8 ≤ arg.toNat) ∧
    ((s08.regs 28).toNat + 16 + 8 ≤ s08.sp.toNat - 4656 ∨ s08.sp.toNat + 8 ≤ (s08.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s08.mem arg.toNat →
      Hw8 [0, s08.sp.toNat - 48 - 384 + 94 + (98 - decLen (val256 s08.mem arg.toNat)), decLen (val256 s08.mem arg.toNat)]
        (s08.regs 28).toNat (s08.sp.toNat - 48 - 384) (rtView rtT s08.mem)) ∧
    (100 ≤ val256 s08.mem arg.toNat → val256 s08.mem arg.toNat < 2 ^ 64 →
      Hw8 [0, s08.sp.toNat - 48 - 384 - 32 + (24 - decLen (val256 s08.mem arg.toNat)), decLen (val256 s08.mem arg.toNat)]
        (s08.regs 28).toNat (s08.sp.toNat - 48 - 384 - 96) (rtView rtT s08.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s08.mem M (rtT ++ [(s08.sp.toNat - 4656, s08.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s08.mem arg.toNat)) →
      DecAt rtT 989280 1002589 960826 p l →
      Hw8 [0, p, l] (s08.regs 28).toNat (s08.sp.toNat - 48) (rtView rtT M))) := by
  rw [hz8, hdl8]
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded8, ?_, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => absurd h (by decide), fun _ _ => ⟨⟨_, rfl⟩, ?_, ?_⟩, ?_⟩
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB]; decide
  · rw [rtView_acc]; decide
  · rw [rtView_acc]; decide
  · intro M p l hMF hSO hDA
    have hl : l = 8 := by
      have h := hSO.1
      have h8 : (decBytes 10000000).length = 8 := hdl8
      omega
    subst hl
    refine ⟨⟨p, rfl⟩, ?_, ?_⟩
    · rw [rtView_acc, hMF.accessible]; decide
    · rw [rtView_acc, hMF.accessible]; decide

open Fv256.ToyRuntimeArm64 in
/-- **Large-value witness**: `z = 10^7` (eight digits, `FormatUint` path): both runtime calls are made and the readiness hypothesis for the
second call is exercised on the string `Dec` returns. -/
theorem big : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s (688 + 48) ∧ StackOK s 4656 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4656) (4656 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4656 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4656 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      H [0, s.sp.toNat - 48 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 48 - 384) (rtView rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      H [0, s.sp.toNat - 48 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 48 - 384 - 96) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [(s.sp.toNat - 4656, s.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s.mem z.toNat)) →
      DecAt rt 989280 1002589 960826 p l →
      H [0, p, l] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt M))) ∧
    100 ≤ val256 s.mem z.toNat :=
  ⟨implAt8, rtT, Hw8, ret, s08, arg, model1_8, model2_8, by rw [linked_eq8]; exact hret8, by rw [linked_eq8]; exact setup8, pre8,
    by rw [hz8]; decide⟩
