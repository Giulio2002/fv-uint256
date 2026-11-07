
/-! ### The large-value path (`z = 10^7`: eight digits, `FormatUint` path, both runtime calls made) -/

def rtT16 : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 16)]

theorem rtView_acc16 (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT16 m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

def Hw8 : RtReady := fun a _ _ view =>
  ((∃ p, a = [0, p, 8]) ∨ (∃ p, a = [0, 1007400, 1, p, 8, 1007400, 1])) ∧
    view.accessible hA 8 true = true ∧ view.accessible hB 16 true = true

open Fv256.ToyRuntimeArm64 in
def implAt8 : List Segment :=
  [{ name := "model-sbts", base := ssAddr, words := sbts8Words }, { name := "model-cb", base := cbAddr, words := cb8Words }]
def linked8 : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt8 }
theorem linked_eq8 : Extracted.program.link implAt8 = linked8 := rfl

theorem copy8_bytes (m : Janus.Arm64.Memory) (a p : Nat) :
    strBytes (m.writeLE a 8 (m.readLE p 8)) a 8 = strBytes m p 8 := by
  apply strBytes_congr
  intro i hi
  have := Janus.Contracts.IfaceModel.bytes_writeLE_readLE m a p 8 i hi
  exact this

theorem cat10_bytes (m : Janus.Arm64.Memory) (q1 q2 p B : Nat) :
    strBytes ((((m.writeLE (B + 8) 8 0).writeLE B 1 (m.bytes q1).toNat).writeLE (B + 1) 8 (m.readLE p 8)).writeLE (B + 9) 1 (m.bytes q2).toNat) B 10
      = strBytes m q1 1 ++ (strBytes m p 8 ++ strBytes m q2 1) := by
  have hb : ∀ j, j < 8 → BitVec.ofNat 8 (m.readLE p 8 / 256 ^ j) = m.bytes (p + j) :=
    fun j hj => Janus.Contracts.IfaceModel.byte_of_readLE m 8 p j hj
  simp only [strBytes, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    Janus.Arm64.Memory.writeLE]
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  have h4 := hb 4 (by omega)
  have h5 := hb 5 (by omega)
  have h6 := hb 6 (by omega)
  have h7 := hb 7 (by omega)
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  have e3 := congrArg BitVec.toNat h3
  have e4 := congrArg BitVec.toNat h4
  have e5 := congrArg BitVec.toNat h5
  have e6 := congrArg BitVec.toNat h6
  have e7 := congrArg BitVec.toNat h7
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.div_one, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  simp
  rw [if_neg (by omega), if_neg (by omega)]
  omega

theorem model1_8 : RtContract (Extracted.program.link implAt8) ssAddr rtT16 4096 Hw8
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw8, rtView_acc16] at ha
  obtain ⟨hshape, hA8, hB8⟩ := ha
  have hlen3 : (argWords s 3).length = 3 := by simp [argWords, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords s 3 = [0, p, 8] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact ⟨p, hp⟩
    · have hp' : argWords s 3 = _ := hp
      rw [hp'] at hlen3; simp at hlen3
  have hargs : argWords s 3 = [0, p, 8] := hp
  simp [slicebytetostringSpec, argWords, wordsFrom] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8
  obtain ⟨h0, h1, h2⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 1).toNat 8 false = true := by
    have h := hs2 (by omega); rw [h2] at h; exact h
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT16, hA]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h1, copy8_bytes]
    refine ⟨⟨trivial, ?_, rfl⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · right; right; right
      exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT16, hA], by omega, by omega⟩

theorem model2_8 : RtContract (Extracted.program.link implAt8) cbAddr rtT16 4096 Hw8 (concatbyteSpec 3) := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw8, rtView_acc16] at ha
  obtain ⟨hshape, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
  have hlen7 : (argWords s 7).length = 7 := by simp [argWords, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords s 7 = [0, 1007400, 1, p, 8, 1007400, 1] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hp' : argWords s 7 = _ := hp
      rw [hp'] at hlen7; simp at hlen7
    · exact ⟨p, hp⟩
  have hargs : argWords s 7 = [0, 1007400, 1, p, 8, 1007400, 1] := hp
  have hargs' : argWords s (concatbyteSpec 3).nargs = [0, 1007400, 1, p, 8, 1007400, 1] := hp
  rw [hargs'] at hstr hbuf
  simp [strPairs, StrsIn, arg] at hstr hbuf
  simp [concatbyteSpec, argWords, wordsFrom, arg] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  obtain ⟨⟨hq1, hq1a⟩, ⟨hp1, hp1a⟩, -⟩ := hstr
  have hqa : s.mem.accessible (s.regs 1).toNat 1 false = true := by rw [h1]; exact hq1a (by omega)
  have hqa5 : s.mem.accessible (s.regs 5).toNat 1 false = true := by rw [h5]; exact hq1a (by omega)
  have hpa : s.mem.accessible (s.regs 3).toNat 8 false = true := by rw [h3]; exact hp1a (by omega)
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true, byte_mod]
    repeat' first
      | exact MemFrame.refl _ _
      | (refine MemFrame.writeLE ?_ _ (r := (6356992, 6357008)) (by simp [rtIf, rtT16, hB]) (by omega) (by omega))
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, byte_mod]
    rw [h5, h1, h3]
    have hc := cat10_bytes s.mem 1007400 1007400 p 6356992
    simp only [Nat.reduceAdd] at hc
    have hl : (strBytes s.mem 1007400 1 ++ (strBytes s.mem p 8 ++ strBytes s.mem 1007400 1)).length = 10 := by simp [strBytes]
    have hr : roundupsize 10 true = 16 := by decide
    refine ⟨hl.symm, fun h => by omega, fun _ h => absurd rfl h, fun _ _ => ⟨by rw [hl, hr], (6356992, 6357008), by simp [rtT16, hB], by omega, by omega⟩, fun _ => ?_⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · exact hc
    · intro i hi
      simp only [Janus.Arm64.Memory.bytes_writeLE]
      have c1 : ¬ (6357001 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6357001 + 1) := by omega
      have c2 : ¬ (6356993 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6356993 + 8) := by omega
      have c3 : ¬ (6356992 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6356992 + 1) := by omega
      have c4 : (6357000 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6357000 + 8) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
      simp


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
    mem := ⟨bytes8, [⟨sp0 - 4688, 4688 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 16, true⟩] ++ dregs⟩ }

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
theorem pre8 : (GuardOK s08 (688 + 80) ∧ StackOK s08 4688 8 ∧ Extracted.program.DataLoaded s08.mem ∧
    Outside (s08.sp.toNat - 4688) (4688 + 8) rtT16 ∧ Outside 989280 256 rtT16 ∧ Outside 1002589 256 rtT16 ∧ Outside 1007400 32 rtT16 ∧ (∀ r ∈ rtT16, 32 ≤ r.1) ∧
    Ptr32 s08.mem arg false ∧ (arg.toNat + 32 ≤ s08.sp.toNat - 4688 ∨ s08.sp.toNat + 8 ≤ arg.toNat) ∧
    ((s08.regs 28).toNat + 16 + 8 ≤ s08.sp.toNat - 4688 ∨ s08.sp.toNat + 8 ≤ (s08.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s08.mem arg.toNat →
      Hw8 [0, s08.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s08.mem arg.toNat)), decLen (val256 s08.mem arg.toNat)]
        (s08.regs 28).toNat (s08.sp.toNat - 80 - 384) (rtView rtT16 s08.mem)) ∧
    (100 ≤ val256 s08.mem arg.toNat → val256 s08.mem arg.toNat < 2 ^ 64 →
      Hw8 [0, s08.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s08.mem arg.toNat)), decLen (val256 s08.mem arg.toNat)]
        (s08.regs 28).toNat (s08.sp.toNat - 80 - 384 - 96) (rtView rtT16 s08.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s08.mem M (rtT16 ++ [(s08.sp.toNat - 4688, s08.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s08.mem arg.toNat)) →
      DecAt rtT16 989280 1002589 960826 p l →
      Hw8 [0, 1007400, 1, p, l, 1007400, 1] (s08.regs 28).toNat (s08.sp.toNat - 80) (rtView rtT16 M))) := by
  rw [hz8, hdl8]
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded8, ?_, ?_, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => absurd h (by decide), fun _ _ => ⟨Or.inl ⟨_, rfl⟩, ?_, ?_⟩, ?_⟩
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB]; decide
  · rw [rtView_acc16]; decide
  · rw [rtView_acc16]; decide
  · intro M p l hMF hSO hDA
    have hl : l = 8 := by
      have h := hSO.1
      have h8 : (decBytes 10000000).length = 8 := hdl8
      omega
    subst hl
    refine ⟨Or.inr ⟨p, rfl⟩, ?_, ?_⟩
    · rw [rtView_acc16, hMF.accessible]; decide
    · rw [rtView_acc16, hMF.accessible]; decide

/-- **Large-value witness**: `z = 10^7` (eight digits, `FormatUint` path): both runtime calls are made and the readiness hypothesis for the
second call is exercised on the string `Dec` returns. -/
theorem big : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s (688 + 80) ∧ StackOK s 4688 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4688) (4688 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ Outside 1007400 32 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      H [0, s.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 80 - 384) (rtView rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      H [0, s.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 80 - 384 - 96) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [(s.sp.toNat - 4688, s.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s.mem z.toNat)) →
      DecAt rt 989280 1002589 960826 p l →
      H [0, 1007400, 1, p, l, 1007400, 1] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt M))) ∧
    100 ≤ val256 s.mem z.toNat :=
  ⟨implAt8, rtT16, Hw8, ret, s08, arg, model1_8, model2_8, by rw [linked_eq8]; exact hret8, by rw [linked_eq8]; exact setup8, pre8,
    by rw [hz8]; decide⟩
