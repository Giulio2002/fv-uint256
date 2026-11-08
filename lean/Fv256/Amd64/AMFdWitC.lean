import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Amd64.MustFromDecimal
import Fv256.Amd64.AMFdWitB
import Fv256.Arm64.WitModel

/-!
# Witness for `FromDecimal` (arm64), part C: a concrete call state (48-digit decimal)

`FromDecimal("<48 digits>")` with the toy runtime `R`, the interface model `(R3 TW)`, a stack window `[lo, hi)`; the memory is
the binary's real data (`DataLoaded`, byte for byte `dataSegByte`) plus synthetic objects (model metadata, heap, multiplier objects, the string).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.FromDecimalSpec Fv256.Amd64.MustFromDecimal

namespace Fv256.Amd64.MFdWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Fv256.Arm64.WitModel

def spW : Nat := 0x100000
def loW : Nat := 0xFD000
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def zW : Nat := 0x300000
def multW : Nat := 0x501000

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the 48-digit input -/
def strBs : List Nat := "123456789012345678901234567890123456789012345678".toList.map Char.toNat

/-- the synthetic contents of the memory outside the binary's data -/
def val (a : Nat) : Nat :=
  if TW ≤ a ∧ a < TW + 48 then (if a = TW then 8 else if a = TW + 20 then 8 else 0)
  else if a = 0x400003 then 0x10
  else if a = 0x100001 then 0x10
  else if 0x301000 ≤ a ∧ a < 0x301000 + 48 then strBs.getD (a - 0x301000) 0
  else if 0x5b7c50 ≤ a ∧ a < 0x5b7c58 then nb 0x4f1a00 0x5b7c50 a
  else if 0x5b7c58 ≤ a ∧ a < 0x5b7c60 then (if a = 0x5b7c58 then 1 else 0)
  else if 0x5b7ba0 ≤ a ∧ a < 0x5b7ba8 then nb 0x4f1a00 0x5b7ba0 a
  else if 0x5b7ba8 ≤ a ∧ a < 0x5b7bb0 then (if a = 0x5b7ba8 then 1 else 0)
  else if 0x5b8588 ≤ a ∧ a < 0x5b85a8 then nb (multW + 32 * ((a - 0x5b8580) / 8 - 1)) 0 ((a - 0x5b8580) % 8)
  else if multW ≤ a ∧ a < multW + 128 then nb (10 ^ (19 * ((a - multW) / 32 + 1))) 0 ((a - multW) % 32)
  else 0

/-- the real byte of the binary's data where there is one, the synthetic one elsewhere -/
def byteAt (a : Nat) : Nat :=
  match Janus.dataSegByte Extracted.program.data a with
  | some n => n
  | none => val a

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (byteAt a),
   (Extracted.program.data.map fun d => (⟨d.base, d.bytes.length, false⟩ : Region)) ++
   [⟨TW, 48, false⟩, ⟨0xFD000, 0x4000, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩,
    ⟨0x301000, 0x1000, false⟩, ⟨BUMP, 0x1000, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0x5b7c50, 16, false⟩, ⟨0x5b7ba0, 16, false⟩, ⟨0x5b7ef0, 16, false⟩, ⟨0x5def20, 4, false⟩, ⟨0x5b8580, 40, false⟩,
    ⟨multW, 128, false⟩]⟩

def retW : Nat := 0x1000
def pSV : BitVec 64 := BitVec.ofNat 64 0x301000
def nSV : BitVec 64 := BitVec.ofNat 64 48
def s0 : State :=
  { regs := fun i => if i = 0 then pSV else if i = 3 then nSV
      else if i = 4 then BitVec.ofNat 64 spW else if i = 14 then BitVec.ofNat 64 gW else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem cfg_lit : cfg = (0x5b7c50, 0x5b7ba0, 0x5b8580, 0x4d78a0, 0x4f1a00, 0x4f19e0, 0x4f09f0, 0x5b7ef0, 0x5def20,
    0x4e6568, 0x4ef9b4, mgA, mvA, newA, w1A, w2A) := by
  rfl

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl


theorem hT_R3 (m : Memory) (g : BitVec 64) (h : (R3 TW).Env m g) :
    isRegularMemory m TW = true ∧ isDirectIface m TW = false ∧ tySize m TW = 8 := by
  obtain ⟨-, d1, -, d3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [isRegularMemory, tyTFlag, d3]; decide
  · simp only [isDirectIface, tyTFlag, d3]; decide
  · simp only [tySize, d1]

theorem outside_of_decide {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L :=
  Janus.Contracts.outside_of_forall h

theorem mod0 : Mod cfg R (R3 TW) TW [] := by
  rw [cfg_lit]
  refine ⟨R3_laws TW (by decide) (by decide), by decide, rfl, ?_, fun r hr => absurd hr (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [rt_eq]
    simp only [R3_priv, List.mem_singleton] at hr
    subst hr
    simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; decide
  · intro r hr
    rw [rt_eq]
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr hne
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [R3_priv]
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | decide
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))


theorem data_small : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0x500000 := by decide

theorem dsb_none (a : Nat) (h : 0x500000 ≤ a) : Janus.dataSegByte Extracted.program.data a = none := by
  unfold Janus.dataSegByte
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have := data_small d hd
  simp only [ite_eq_right_iff]
  intro h2; omega

theorem val_big (a : Nat) (h : 0x600000 ≤ a) : val a = 0 := by
  unfold val
  rw [if_neg (show ¬(TW ≤ a ∧ a < TW + 48) by simp only [TW]; omega),
    if_neg (show ¬(a = 0x400003) by omega),
    if_neg (show ¬(a = 0x100001) by omega),
    if_neg (show ¬(0x301000 ≤ a ∧ a < 0x301000 + 48) by omega),
    if_neg (show ¬(0x5b7c50 ≤ a ∧ a < 0x5b7c58) by omega),
    if_neg (show ¬(0x5b7c58 ≤ a ∧ a < 0x5b7c60) by omega),
    if_neg (show ¬(0x5b7ba0 ≤ a ∧ a < 0x5b7ba8) by omega),
    if_neg (show ¬(0x5b7ba8 ≤ a ∧ a < 0x5b7bb0) by omega),
    if_neg (show ¬(0x5b8588 ≤ a ∧ a < 0x5b85a8) by omega),
    if_neg (show ¬(multW ≤ a ∧ a < multW + 128) by simp only [multW]; omega)]

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (byteAt i) = 0
  have : 0x600000 ≤ i := by simp only [HEAP] at h; omega
  simp only [byteAt, dsb_none i (by omega), val_big i this]; rfl

theorem dataLoaded0 : Extracted.program.DataLoaded mem0 := by
  refine Janus.Amd64.Program.DataLoaded_of_dataSegByte (by unfold Janus.DataSegsDisjoint; decide) (fun d hd => ?_) (by decide) (fun a n h => ?_)
  · have hs := data_small d hd
    refine List.any_eq_true.2 ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_left _ (List.mem_map.2 ⟨d, hd, rfl⟩), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by omega⟩, trivial⟩
  · show (BitVec.ofNat 8 (byteAt a)).toNat = n % 256
    simp only [byteAt, h, BitVec.toNat_ofNat]

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)

theorem static0 : StaticOK cfg (R3 TW) TW s0.mem := by
  rw [cfg_lit]
  exact ⟨by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env0 : Env cfg R (R3 TW) TW 0x400 [] loW hiW s0 := by
  rw [cfg_lit]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_,
    by decide, ?_, static0, ?_, inv0, fun r hr => absurd hr (by simp)⟩
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact ⟨by decide, by decide, by decide, by decide⟩

theorem mult0 : MultOK cfg loW loW hiW s0.mem := by
  rw [cfg_lit]
  refine ⟨by decide, ?_, ?_⟩
  · apply outside_of_decide; decide
  · intro k h1 h2
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    all_goals refine ⟨by decide, by decide, by decide, ?_⟩
    all_goals (apply outside_of_decide; decide)

theorem maxdig0 : ∀ k, k < 78 → s0.mem.readLE (cfg.maxStr + k) 1 = Fv256.I.maxDigit k := by
  rw [cfg_lit]
  decide

theorem chunk_bs : ∀ sl, sl ≤ 19 → blockSize sl true + blockSize 48 false ≤ 0x400 - blockSize 32 true := by decide

theorem chunk0 : ChunkAll cfg R (R3 TW) [] (0x400 - blockSize 32 true) pSV.toNat nSV.toNat loW hiW s0.mem := by
  rw [cfg_lit]
  intro sp sl h1 h2 h3 h4
  have e1 : pSV.toNat = 0x301000 := by decide
  have e2 : nSV.toNat = 48 := by decide
  rw [e1] at h1 h2; rw [e2] at h2
  have hsp : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  have hsl : (BitVec.ofNat 64 sl).toNat = sl := Nat.mod_eq_of_lt (by omega)
  have hacc : s0.mem.accessible 0x301000 48 false = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsl]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h3, h4, rfl⟩))))
  · intro q; simp only [hsl, hsp]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, q, sp, sl, rfl, h3, h4⟩))))
  · simp only [hsl]; exact chunk_bs sl h4
  · simp only [hsp, hsl]; exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  · simp only [hsp, hsl]; omega
  · simp only [hsp, hsl]; simp only [loW, hiW]; omega
  · left; simp only [hsp, hsl, rt_eq]; apply outside_of_decide
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [HEAP, HEND, HSIZE, BUMP, WBUF] <;> omega
  · simp only [hsp, hsl]; simp only [R3_priv]; apply outside_of_decide
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr; simp only [TW]; omega

theorem initDone0 : InitDone cfg (R3 TW) s0.mem := by
  rw [cfg_lit]
  exact ⟨by decide, by decide, by decide, by decide, fun r hr => by simp only [R3_priv, List.mem_singleton] at hr; subst hr; simp⟩

theorem ioeof0 : s0.mem.readLE cfg.ioEOF 8 = 0x4f1a00 := by rw [cfg_lit]; decide
theorem errbig0 : s0.mem.readLE cfg.errBig 8 = 0x4f1a00 := by rw [cfg_lit]; decide

theorem panicInit0 : PanicInit cfg R (R3 TW) loW hiW s0.mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w = 0x4f1a00 := by
      rcases hw with h | h
      · rw [h]; exact ioeof0
      · rw [h]; exact errbig0
    subst hw'
    refine ⟨by decide, by decide, ?_, ?_⟩
    · rw [rt_eq]; apply outside_of_decide; decide
    · apply outside_of_decide; decide
  · rw [cfg_lit, rt_eq]; apply outside_of_decide; decide
  · rw [cfg_lit]; apply outside_of_decide; decide
  · rw [cfg_lit]; simp only [R3_priv]; apply outside_of_decide; decide
  · rw [cfg_lit]; decide

theorem pre0 : Fv256.Amd64.MustFromDecimal.Pre R (R3 TW) TW 0x400 [] loW hiW pSV nSV s0 := by
  have hm := maxdig0
  have hc := chunk0
  have hi := initDone0
  have hp := panicInit0
  unfold Fv256.Amd64.MustFromDecimal.Pre PreC0
  refine ⟨⟨rfl, rfl, mod0, env0, ?_, ?_, ?_, ?_, mult0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi, ?_, ?_, ?_, hm, ?_,
    ?_, ?_, hc⟩, dataLoaded0, hp⟩
  all_goals first
    | decide
    | (apply outside_of_decide; decide)
    | (show cfg.newobject = newA ∧ _ ∨ _
       rw [cfg_lit]; exact Or.inr (Or.inl ⟨rfl, rfl⟩))
    | (intro k h1 h2
       rw [cfg_lit, rt_eq]
       have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
       rcases hk with rfl | rfl | rfl | rfl <;> (apply outside_of_decide; decide))
    | (exact ⟨by decide, by decide⟩)
    | (left; rw [rt_eq]; apply outside_of_decide; decide)

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by rw [linked_eq]; decide)

theorem setup : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [pSV, nSV] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl, rfl⟩

/-- pins the type of an existential variable of `nonvacuous` -/
def pinPanicRuntime (_k : Janus.Spec.PanicRuntime) : Prop := True

open Fv256.CallSites

/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `RIP` at the stub's entry and the stub's argument registers. -/
def csNew : State := { s0 with rip := BitVec.ofNat 64 newA, regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else s0.regs i }
def csW1 : State := { s0 with rip := BitVec.ofNat 64 w1A }
def csW2 : State := { s0 with rip := BitVec.ofNat 64 w2A }
def csMg : State := { s0 with rip := BitVec.ofNat 64 mgA, regs := fun i => if i = 0 then 1 else if i = 3 then 0 else if i = 1 then 0 else s0.regs i }
def csMv : State := { s0 with rip := BitVec.ofNat 64 mvA, regs := fun i => if i = 0 then BitVec.ofNat 64 zW else if i = 3 then BitVec.ofNat 64 0x301000 else if i = 1 then 1 else s0.regs i }
def csCm : State := { s0 with rip := BitVec.ofNat 64 cmA, regs := fun i => if i = 0 then 0 else if i = 3 then 0 else if i = 1 then 0 else if i = 7 then 0 else s0.regs i }
def csIf : State := { s0 with rip := BitVec.ofNat 64 ifA, regs := fun i => if i = 0 then 0 else s0.regs i }
theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr_new]; rfl
theorem csW1_rip : csW1.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") := by rw [addr_w1]; rfl
theorem csW2_rip : csW2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") := by rw [addr_w2]; rfl
theorem csMg_rip : csMg.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") := by rw [addr_mg]; rfl
theorem csMv_rip : csMv.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") := by rw [addr_mv]; rfl
theorem csCm_rip : csCm.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") := by rw [addr_cm]; rfl
theorem csIf_rip : csIf.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") := by rw [addr_if]; rfl
set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_new]; exact Or.inl (⟨rfl, by decide⟩), inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 csMg :=
  ⟨⟨by decide, by decide, Or.inl (by decide)⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_mg]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, 1, by decide, by decide, by decide⟩))))), inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 csMv :=
  ⟨by decide, by rw [addr_mv]; exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, zW, 0x301000, 1, by decide, by decide, by decide⟩))))), inv0, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩, by decide,
    by decide, by decide, by rw [rt_eq]; simp only [calleeStack64, outside_cons, outside_nil]; decide, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide), by simp only [outside_cons, outside_nil]; decide⟩

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 :=
  ⟨by decide, by rw [addr_w1]; exact Or.inr (Or.inr (Or.inl (⟨rfl, by decide⟩))), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 :=
  ⟨by decide, by rw [addr_w2]; exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by decide⟩)))), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre64 16 csCm :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite (R3 TW) csIf :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun h => absurd (by decide) h⟩

/-- The statement of the witness theorem `nonvacuous` (spelled out there). -/
theorem nonvacuous_core : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (pS nS : BitVec 64) (P : Janus.Spec.PanicRuntime) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pS, nS] s ∧
    (pinPanicRuntime P ∧ Fv256.Amd64.MustFromDecimal.Pre R R2 T b L lo hi pS nS s) :=
  ⟨implA, R, R3 TW, TW, 0x400, [], loW, hiW, pSV, nSV, Janus.Contracts.PanicModel.P0 [] 0, retW, s0,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, ⟨[], 0x400, csNew, csNew_rip, csNew_pre⟩, ⟨[], 0x400, csMg, csMg_rip, csMg_pre⟩, ⟨[], 0x400, csMv, csMv_rip, csMv_pre⟩, ⟨[], 0x400, csW1, csW1_rip, csW1_pre⟩, ⟨[], 0x400, csW2, csW2_rip, csW2_pre⟩, ⟨csCm, csCm_rip, csCm_pre⟩, ⟨csIf, csIf_rip, csIf_pre⟩, hret, setup, ⟨trivial, pre0⟩⟩

end Fv256.Amd64.MFdWit
