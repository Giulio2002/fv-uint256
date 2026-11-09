import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.ScanWitB
import Fv256.Proofs.Arm64.ScanSciBase
import Fv256.Proofs.Arm64.ScanSpec

/-!
# Witness for `Scan` (arm64), part C: the memory and the call states

One memory `mem0` for all witnesses: the binary's read-only data (`DataLoaded`, byte for byte `dataSegByte`), the interface
model's type descriptor at `TW`, the window, the goroutine, the receiver, the strings, a slice, the sentinel errors, the multiplier
table and the toy allocator's metadata/heap.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.WitModel Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanSciSpec

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Scan.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy

def spW : Nat := 0x100000
def loW : Nat := 0xFDE00
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def zW : Nat := 0x300000
def multW : Nat := 0x501000
def strW : Nat := 0x301000
def hdrW : Nat := 0x302000
def slW : Nat := 0x303000
def bufW : Nat := 0x304000
def retW : Nat := 0x1000
def str2W : Nat := 0x305000
def hdr2W : Nat := 0x306000

/-- the scientific input of the string witness: 12 digits, `e`, exponent 5 -/
def strBs : List Nat := "123456789012e5".toList.map Char.toNat
/-- the input of the `[]byte` witness: 46 digits, `e`, exponent 5 (48 bytes) -/
def strBs2 : List Nat := "1234567890123".toList.map Char.toNat
def bytBs : List Nat := "1234567890123456789012345678901234567890123456e5".toList.map Char.toNat

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the synthetic contents of the memory outside the binary's data -/
def val (a : Nat) : Nat :=
  if TW ≤ a ∧ a < TW + 48 then (if a = TW then 8 else if a = TW + 20 then 8 else 0)
  else if strW ≤ a ∧ a < strW + 16 then strBs.getD (a - strW) 0
  else if hdrW ≤ a ∧ a < hdrW + 8 then nb strW hdrW a
  else if hdrW + 8 ≤ a ∧ a < hdrW + 16 then nb strBs.length (hdrW + 8) a
  else if str2W ≤ a ∧ a < str2W + 16 then strBs2.getD (a - str2W) 0
  else if hdr2W ≤ a ∧ a < hdr2W + 8 then nb str2W hdr2W a
  else if hdr2W + 8 ≤ a ∧ a < hdr2W + 16 then nb strBs2.length (hdr2W + 8) a
  else if slW ≤ a ∧ a < slW + 8 then nb bufW slW a
  else if slW + 8 ≤ a ∧ a < slW + 16 then nb 48 (slW + 8) a
  else if slW + 16 ≤ a ∧ a < slW + 24 then nb 48 (slW + 16) a
  else if bufW ≤ a ∧ a < bufW + 48 then bytBs.getD (a - bufW) 0
  else if a = 0x400003 then 0x10
  else if 0x1b5c10 ≤ a ∧ a < 0x1b5c20 then (if a = 0x1b5c10 ∨ a = 0x1b5c18 then 1 else 0)
  else if 0x1b5b60 ≤ a ∧ a < 0x1b5b70 then (if a = 0x1b5b60 ∨ a = 0x1b5b68 then 1 else 0)
  else if 0x1b6548 ≤ a ∧ a < 0x1b6568 then nb (multW + 32 * ((a - 0x1b6540) / 8 - 1)) 0 ((a - 0x1b6540) % 8)
  else if multW ≤ a ∧ a < multW + 128 then nb (10 ^ (19 * ((a - multW) / 32 + 1))) 0 ((a - multW) % 32)
  else 0

def byteAt (a : Nat) : Nat :=
  match Janus.dataSegByte Extracted.program.data a with
  | some n => n
  | none => val a

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (byteAt a),
   (Extracted.program.data.map fun d => (⟨d.base, d.bytes.length, false⟩ : Region)) ++
   [⟨TW, 48, false⟩, ⟨0xFD000, 0x4000, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩, ⟨strW, 0x1000, false⟩, ⟨hdrW, 16, false⟩, ⟨str2W, 0x1000, false⟩, ⟨hdr2W, 16, false⟩,
    ⟨slW, 24, false⟩, ⟨bufW, 0x1000, false⟩, ⟨0xf8000, 0x1000, false⟩, ⟨BUMP, 0x1000, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0x1b5c10, 16, false⟩, ⟨0x1b5b60, 16, false⟩, ⟨0x1b5eb0, 16, false⟩, ⟨0x1e34c0, 4, false⟩, ⟨0x1b6540, 40, false⟩,
    ⟨multW, 128, false⟩]⟩


def tyS : Nat := janus_eval% Extracted.dataAddr.«type:string#f88732b8»
def tyB : Nat := janus_eval% Extracted.dataAddr.«type:[]uint8#7efbbf65»
def tyU : Nat := janus_eval% Extracted.dataAddr.«type:uint8#6a8c7679»
def itabE : Nat := janus_eval% Extracted.dataAddr.«go:itab.*errors.errorString,error»
def stW : Nat := janus_eval% Extracted.dataAddr.«runtime.staticuint64s»

def zV : BitVec 64 := BitVec.ofNat 64 zW
def dwS : BitVec 64 := BitVec.ofNat 64 hdrW
def dwB : BitVec 64 := BitVec.ofNat 64 slW

/-- the call state: receiver `zV`, type word `tw`, data word `dw` -/
def st (tw dw : BitVec 64) : State :=
  { regs := fun i => if i = 0 then zV else if i = 1 then tw else if i = 2 then dw
      else if i = 28 then BitVec.ofNat 64 gW else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 spW, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem cfg_lit : cfg = (SfdCfg.mk 0x1b5c10 0x1b5b60 0x1b6540 0xdc840 0xf6940 0xf6920 0xf5940 0x1b5eb0 0x1e34c0 0xeb483
    0xf490b mgA mvA newA w1A w2A) := by
  rfl

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem outside_of_decide {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L :=
  Janus.Contracts.outside_of_forall h

theorem hT_R3 (m : Memory) (g : BitVec 64) (h : (R3 TW).Env m g) :
    isRegularMemory m TW = true ∧ isDirectIface m TW = false ∧ tySize m TW = 8 := by
  obtain ⟨-, d1, -, d3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [isRegularMemory, tyTFlag, d3]; decide
  · simp only [isDirectIface, tyTFlag, d3]; decide
  · simp only [tySize, d1]

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
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))


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
    if_neg (show ¬(strW ≤ a ∧ a < strW + 16) by simp only [strW]; omega),
    if_neg (show ¬(hdrW ≤ a ∧ a < hdrW + 8) by simp only [hdrW]; omega),
    if_neg (show ¬(hdrW + 8 ≤ a ∧ a < hdrW + 16) by simp only [hdrW]; omega),
    if_neg (show ¬(str2W ≤ a ∧ a < str2W + 16) by simp only [str2W]; omega),
    if_neg (show ¬(hdr2W ≤ a ∧ a < hdr2W + 8) by simp only [hdr2W]; omega),
    if_neg (show ¬(hdr2W + 8 ≤ a ∧ a < hdr2W + 16) by simp only [hdr2W]; omega),
    if_neg (show ¬(slW ≤ a ∧ a < slW + 8) by simp only [slW]; omega),
    if_neg (show ¬(slW + 8 ≤ a ∧ a < slW + 16) by simp only [slW]; omega),
    if_neg (show ¬(slW + 16 ≤ a ∧ a < slW + 24) by simp only [slW]; omega),
    if_neg (show ¬(bufW ≤ a ∧ a < bufW + 48) by simp only [bufW]; omega),
    if_neg (show ¬(a = 0x400003) by omega),
    if_neg (show ¬(0x1b5c10 ≤ a ∧ a < 0x1b5c20) by omega),
    if_neg (show ¬(0x1b5b60 ≤ a ∧ a < 0x1b5b70) by omega),
    if_neg (show ¬(0x1b6548 ≤ a ∧ a < 0x1b6568) by omega),
    if_neg (show ¬(multW ≤ a ∧ a < multW + 128) by simp only [multW]; omega)]

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (byteAt i) = 0
  have : 0x600000 ≤ i := by simp only [HEAP] at h; omega
  simp only [byteAt, dsb_none i (by omega), val_big i this]; rfl

theorem inv0 (tw dw : BitVec 64) : R.inv 0x400 [] ((st tw dw).regs 28).toNat (view R.rt [] (st tw dw).mem) := by
  refine toyInv_init (m := mem0) (g := ((st tw dw).regs 28).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)


theorem static_b : StaticOK cfg (R3 TW) TW (st 0#64 0#64).mem := by
  show StaticOK cfg (R3 TW) TW mem0
  rw [cfg_lit]
  exact ⟨by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env_b : Env cfg R (R3 TW) TW 0x400 [] loW hiW (st 0#64 0#64) := by
  rw [cfg_lit]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_,
    by decide, ?_, ?_, ?_, ?_, fun r hr => absurd hr (by simp)⟩
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have := static_b; rw [cfg_lit] at this; exact this
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · have := inv0 0#64 0#64; exact this

theorem static0 (tw dw : BitVec 64) : StaticOK cfg (R3 TW) TW (st tw dw).mem := static_b
theorem env0 (tw dw : BitVec 64) : Env cfg R (R3 TW) TW 0x400 [] loW hiW (st tw dw) := env_b

theorem mult0 : MultOK cfg zV.toNat loW hiW mem0 := by
  rw [cfg_lit]
  refine ⟨by decide, ?_, ?_⟩
  · apply outside_of_decide; decide
  · intro k h1 h2
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    all_goals refine ⟨by decide, by decide, by decide, ?_⟩
    all_goals (apply outside_of_decide; decide)

theorem maxdig0 : ∀ k, k < 78 → mem0.readLE (0xf490b + k) 1 = Fv256.I.maxDigit k := by
  decide


def twS : BitVec 64 := BitVec.ofNat 64 tyS
def pSV : BitVec 64 := BitVec.ofNat 64 strW
def nSV : BitVec 64 := BitVec.ofNat 64 strBs.length

theorem hdrP_S : hdrP (st twS dwS) dwS = pSV := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrP pSV; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE hdrW 8) % 2 ^ 64 = strW % 2 ^ 64
  have : mem0.readLE hdrW 8 = strW := by decide
  rw [this]

theorem hdrN_S : hdrN (st twS dwS) dwS = nSV := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrN nSV; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE (hdrW + 8) 8) % 2 ^ 64 = strBs.length % 2 ^ 64
  have : mem0.readLE (hdrW + 8) 8 = strBs.length := by decide
  rw [this]

theorem chunk_bs : ∀ sl, sl ≤ 19 → blockSize sl true + blockSize 48 false ≤ 0x400 := by decide

theorem chunkS : ChunkAll cfg R (R3 TW) [] 0x400 pSV.toNat nSV.toNat loW hiW mem0 := by
  intro sp sl h1 h2 h3 h4
  have e1 : pSV.toNat = strW := by decide
  have e2 : nSV.toNat = strBs.length := by decide
  have e3 : strBs.length = 14 := by decide
  simp only [e1, e2, e3, strW] at h1 h2
  have hsp : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  have hsl : (BitVec.ofNat 64 sl).toNat = sl := Nat.mod_eq_of_lt (by omega)
  have hacc : mem0.accessible strW 14 false = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsl]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h3, h4, rfl⟩)))
  · intro q; simp only [hsl, hsp]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, sp, sl, h3, h4, rfl⟩))))
  · simp only [hsl]; exact Nat.le_trans (chunk_bs sl h4) (Nat.le_refl _)
  · simp only [hsp, hsl]; exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by simp only [strW]; omega) (by simp only [strW]; omega)
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


theorem top0S : TopPre0 cfg R (R3 TW) TW 0x400 [] loW hiW zV pSV nSV (viewS (st twS dwS) pSV nSV) := by
  have hm := maxdig0
  have hc := chunkS
  unfold TopPre0
  refine ⟨by simp [viewS, setReg_apply, st], by simp [viewS, setReg_apply], by simp [viewS, setReg_apply],
    mod0, env0 twS dwS, by decide, by decide, mult0, by decide, ?_, by decide, ?_, ?_, hm, by decide, ?_,
    ⟨by decide, by decide⟩, by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, hc⟩
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide


theorem initDone0 : InitDone cfg (R3 TW) mem0 :=
  ⟨by decide, by decide, by decide, by decide, fun r hr => by simp only [R3_priv, List.mem_singleton] at hr; subst hr; simp⟩

theorem retAddr : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by decide)

theorem setup (tw dw : BitVec 64) :
    CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, tw, dw] (st tw dw) :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | r <;> simp [st] at h ⊢ <;> omega⟩

theorem pre_base : loW + 4720 ≤ (st 0#64 0#64).sp.toNat ∧ (st 0#64 0#64).sp.toNat + 32 ≤ hiW ∧ hiW ≤ 2 ^ 48 ∧
    (st 0#64 0#64).sp.toNat % 16 = 0 ∧ GuardOK (st 0#64 0#64) 80 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  unfold GuardOK
  exact ⟨by decide, by decide, by decide⟩

theorem pre_common (tw dw : BitVec 64) :
    (st tw dw).regs 0 = zV ∧ (st tw dw).regs 1 = tw ∧ (st tw dw).regs 2 = dw ∧ loW + 4720 ≤ (st tw dw).sp.toNat ∧
      (st tw dw).sp.toNat + 32 ≤ hiW ∧ hiW ≤ 2 ^ 48 ∧ (st tw dw).sp.toNat % 16 = 0 ∧ GuardOK (st tw dw) 80 :=
  ⟨rfl, rfl, rfl, pre_base⟩

theorem dataLoaded0 : Extracted.program.DataLoaded mem0 := by
  refine Janus.Program.DataLoaded_of_dataSegByte (by unfold Janus.DataSegsDisjoint; decide) (fun d hd => ?_) (by decide) (fun a n h => ?_)
  · have hs := data_small d hd
    refine List.any_eq_true.2 ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_left _ (List.mem_map.2 ⟨d, hd, rfl⟩), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by omega⟩, trivial⟩
  · show (BitVec.ofNat 8 (byteAt a)).toNat = n % 256
    simp only [byteAt, h, BitVec.toNat_ofNat]


theorem pageS : Fv256.IndexByte.PageReadable mem0 pSV.toNat nSV.toNat := by
  unfold Fv256.IndexByte.PageReadable
  right
  exact ⟨by decide, by decide⟩

theorem preS : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
    (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twS dwS (st twS dwS) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := pre_common twS dwS
  refine ⟨a, b, c, d, e, f, g, h, Or.inr (Or.inl ⟨by decide, ⟨by decide, by decide⟩, Or.inr (by decide), ?_, initDone0, ?_⟩)⟩
  · rw [hdrP_S, hdrN_S]; exact top0S
  · rw [hdrP_S, hdrN_S]; exact pageS


/-- the contracts of `Scan.correctness` hold of the stub runtime -/
theorem contracts_ok :
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.ifaceeq") (R3 TW) ∧
    NewobjectLiveContract (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.slicebytetostring") 4096 R
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl implA) (Extracted.program.contractAddr "runtime.cmpstring") 16 :=
  ⟨by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_sb]; exact model_sb, by rw [addr_cm]; exact hcmp⟩

/-! ### Call-site states (U-WITNESS-CALLSITE), shared by the five `Scan` witnesses: the call state `st 0#64 0#64` with `PC` at each runtime
stub's entry and the argument registers of a request the toy runtime `R` serves; live set `[]`, budget `0x400`. -/
-- CALLSITE-BLOCK
def csB : State := st 0#64 0#64
def csNew : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject"), regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else csB.regs i }
def csW1 : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }
def csMg : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc"), regs := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 0 else csB.regs i }
def csMv : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove"), regs := fun i => if i = 0 then BitVec.ofNat 64 0xFD000 else if i = 1 then BitVec.ofNat 64 strW else if i = 2 then 1 else csB.regs i }
def csCm : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring"), regs := fun i => if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 0 else csB.regs i }
def csIf : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq"), regs := fun i => if i = 0 then 0 else csB.regs i }
def csSb : State := { csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring"), regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 strW else if i = 2 then 48 else csB.regs i }

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), typeOK_of (by decide) (by decide), by decide⟩, ⟨guardOK_of (by decide) (by decide) (by decide), (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩,
    ?_, inv0 0#64 0#64, by decide, liveSep_nil _, (by intro r hr; rw [rt_eq]; simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩
  rw [addr_new]; exact Or.inl (⟨rfl, Or.inl (by decide)⟩)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, inv0 0#64 0#64, liveSep_nil _, (by intro r hr; rw [rt_eq]; simp only [List.mem_singleton] at hr; subst hr; simp only [outside_cons, outside_nil]; decide)⟩
  rw [addr_w1]; exact Or.inr (Or.inl (⟨rfl, rfl⟩))

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, inv0 0#64 0#64, liveSep_nil _, (by intro r hr; rw [rt_eq]; simp only [List.mem_singleton] at hr; subst hr; simp only [outside_cons, outside_nil]; decide)⟩
  rw [addr_w2]; exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl⟩)))

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 csMg := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide, Or.inl (by decide)⟩, ⟨guardOK_of (by decide) (by decide) (by decide), (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩,
    ?_, inv0 0#64 0#64, by decide, liveSep_nil _, (by intro r hr; rw [rt_eq]; simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩
  rw [addr_mg]; exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, 1, by decide, by decide, by decide⟩))))

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 csMv := by
  refine ⟨⟨(Janus.Spec.guardOK_iff _ _).1 (guardOK_of (by decide) (by decide) (by decide)), callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩, ⟨?_, inv0 0#64 0#64, liveSep_nil _, (by intro r hr; rw [rt_eq]; simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩,
    ⟨by decide, by decide, (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩, ⟨by decide, by decide, (by simp only [calleeStack, outside_cons, outside_nil]; decide), Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩⟩
  rw [addr_mv]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, 0xFD000, strW, 1, by decide, by decide, by decide⟩)))))

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 csCm :=
  ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Or.inl (by decide), Or.inl (by decide)⟩

theorem r3env : (R3 TW).Env csB.mem (csB.regs 28) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := env0 0#64 0#64
  exact h

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite (R3 TW) csIf := by
  refine ⟨⟨r3env, (Janus.Spec.guardOK_iff _ _).1 (guardOK_of (by decide) (by decide) (by decide)), callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩, fun h => absurd (by decide) h⟩
  simp only [R3_priv, R3_depth, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive (Extracted.program.contractAddr "runtime.slicebytetostring") [] 0x400 csSb := by
  have hok : R.ok (Extracted.program.contractAddr "runtime.slicebytetostring") (argWords csSb 3) := by
    rw [addr_sb]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, 0, strW, by decide⟩)))))
  unfold RtLivePre
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ⟨guardOK_of (by decide) (by decide) (by decide), (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩, hok, inv0 0#64 0#64, by decide, liveSep_nil _, (by intro r hr; rw [rt_eq]; simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), by decide, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside, calleeStack, outside_cons, outside_nil]
    decide

/-- The statement of the witness theorem `Scan.Witness.nonvacuous` (spelled out there), for the string case. -/
theorem nonvacuous_core_str : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") 4096 R
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
      (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
      Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧
    Extracted.program.DataLoaded s.mem :=
  ⟨implA, R, R3 TW, TW, 0x400, [], loW, hiW, zV, twS, dwS, retW, st twS dwS, implOK, contracts_ok.1, contracts_ok.2.1,
    contracts_ok.2.2.1, contracts_ok.2.2.2.1, contracts_ok.2.2.2.2.1, contracts_ok.2.2.2.2.2.1, contracts_ok.2.2.2.2.2.2.1,
    contracts_ok.2.2.2.2.2.2.2, retAddr, setup twS dwS, preS, dataLoaded0⟩

end Fv256.Arm64.Scan.Witness
