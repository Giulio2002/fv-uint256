import Extracted
import Fv256.Arm64.FromDecimal
import Fv256.Arm64.FdWitB
import Fv256.Arm64.WitModel

/-!
# Witness for `FromDecimal` (arm64), part C: a concrete call state (48-digit decimal)

`FromDecimal("<48 digits>")` with the toy runtime `R`, the interface model `(R3 TW)`, a stack window `[lo, hi)`; the memory is
the binary's real data (`DataLoaded`, byte for byte `dataSegByte`) plus synthetic objects (model metadata, heap, multiplier objects, the string).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromDecimalSpec Fv256.Arm64.FromDecimal

namespace Fv256.Arm64.FdWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Fv256.Arm64.WitModel

def spW : Nat := 0x100000
def loW : Nat := 0xFEE00
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
  else if 0x301000 ≤ a ∧ a < 0x301000 + 48 then strBs.getD (a - 0x301000) 0
  else if 0x1b5c10 ≤ a ∧ a < 0x1b5c18 then nb 0xf6940 0x1b5c10 a
  else if 0x1b5c18 ≤ a ∧ a < 0x1b5c20 then (if a = 0x1b5c18 then 1 else 0)
  else if 0x1b5b60 ≤ a ∧ a < 0x1b5b68 then nb 0xf6940 0x1b5b60 a
  else if 0x1b5b68 ≤ a ∧ a < 0x1b5b70 then (if a = 0x1b5b68 then 1 else 0)
  else if 0x1b6548 ≤ a ∧ a < 0x1b6568 then nb (multW + 32 * ((a - 0x1b6540) / 8 - 1)) 0 ((a - 0x1b6540) % 8)
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
    ⟨0x1b5c10, 16, false⟩, ⟨0x1b5b60, 16, false⟩, ⟨0x1b5eb0, 16, false⟩, ⟨0x1e34c0, 4, false⟩, ⟨0x1b6540, 40, false⟩,
    ⟨multW, 128, false⟩]⟩

def pSV : BitVec 64 := BitVec.ofNat 64 0x301000
def nSV : BitVec 64 := BitVec.ofNat 64 48
def retW : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then pSV else if i = 1 then nSV
      else if i = 28 then BitVec.ofNat 64 gW else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 spW, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem cfg_lit : cfg = (SfdCfg.mk 0x1b5c10 0x1b5b60 0x1b6540 0xdc840 0xf6940 0xf6920 0xf5940 0x1b5eb0 0x1e34c0 0xeb483
    0xf490b mgA mvA newA w1A w2A) := by
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
  refine ⟨R3_laws TW (by decide) (by decide), by decide, by decide, rfl, ?_, fun r hr => absurd hr (by simp), ?_, ?_, ?_, ?_, ?_, ?_, hT_R3⟩
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


theorem data_small : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0x200000 := by decide

theorem dsb_none (a : Nat) (h : 0x200000 ≤ a) : Janus.dataSegByte Extracted.program.data a = none := by
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
    if_neg (show ¬(0x301000 ≤ a ∧ a < 0x301000 + 48) by omega),
    if_neg (show ¬(0x1b5c10 ≤ a ∧ a < 0x1b5c18) by omega),
    if_neg (show ¬(0x1b5c18 ≤ a ∧ a < 0x1b5c20) by omega),
    if_neg (show ¬(0x1b5b60 ≤ a ∧ a < 0x1b5b68) by omega),
    if_neg (show ¬(0x1b5b68 ≤ a ∧ a < 0x1b5b70) by omega),
    if_neg (show ¬(0x1b6548 ≤ a ∧ a < 0x1b6568) by omega),
    if_neg (show ¬(multW ≤ a ∧ a < multW + 128) by simp only [multW]; omega)]

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (byteAt i) = 0
  have : 0x600000 ≤ i := by simp only [HEAP] at h; omega
  simp only [byteAt, dsb_none i (by omega), val_big i this]; rfl

theorem dataLoaded0 : Extracted.program.DataLoaded mem0 := by
  refine Janus.Program.DataLoaded_of_dataSegByte (by unfold Janus.DataSegsDisjoint; decide) (fun d hd => ?_) (by decide) (fun a n h => ?_)
  · have hs := data_small d hd
    refine List.any_eq_true.2 ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_left _ (List.mem_map.2 ⟨d, hd, rfl⟩), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by omega⟩, trivial⟩
  · show (BitVec.ofNat 8 (byteAt a)).toNat = n % 256
    simp only [byteAt, h, BitVec.toNat_ofNat]

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
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

theorem pre0 : Fv256.Arm64.FromDecimal.Pre R (R3 TW) TW 0x400 [] loW hiW pSV nSV s0 := by
  have hm := maxdig0
  have hc := chunk0
  have hi := initDone0
  unfold Fv256.Arm64.FromDecimal.Pre PreC
  refine ⟨⟨?_, ?_, rfl, rfl, mod0, env0, ?_, ?_, ?_, ?_, mult0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi, ?_, ?_, ?_, hm, ?_,
    ?_, ?_, ?_, hc⟩, dataLoaded0⟩
  all_goals first | decide | (apply outside_of_decide; decide) | skip
  · show cfg.newobject = newA ∧ _ ∨ _
    rw [cfg_lit]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · intro k h1 h2
    rw [cfg_lit, rt_eq]
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl <;> (apply outside_of_decide; decide)
  · left; rw [rt_eq]; apply outside_of_decide; decide

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [pSV, nSV] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

/-- The statement of the witness theorem `nonvacuous` (spelled out there). -/
theorem nonvacuous_core : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (pS nS : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pS, nS] s ∧
    Fv256.Arm64.FromDecimal.Pre R R2 T b L lo hi pS nS s :=
  ⟨implA, R, R3 TW, TW, 0x400, [], loW, hiW, pSV, nSV, retW, s0, implOK,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, hret, setup, pre0⟩

end Fv256.Arm64.FdWit
