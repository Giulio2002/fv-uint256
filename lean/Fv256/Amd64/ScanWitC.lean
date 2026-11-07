import Extracted
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanWitB
import Fv256.Amd64.WitModel

/-!
# Witness for `Scan` (amd64), part C: the memory and the call states

One memory `mem0` for all witnesses: the binary's read-only data (`DataLoaded`, byte for byte `dataSegByte`), the interface model's
metadata, the stack window, the goroutine and its TLS slot, the receiver, the strings, a slice, the static objects the proof reads
(at the extraction's own addresses), the multiplier objects and the toy allocator's metadata/heap.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.WitModel

namespace Fv256.Amd64.Scan.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64 Fv256.Amd64.WitModel

def spW : Nat := 0x100000
def loW : Nat := 0xFD000
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def fsW : Nat := 0x210008
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
/-- the input of the no-exponent witness -/
def strBs2 : List Nat := "1234567890123".toList.map Char.toNat
/-- the input of the `[]byte` witness: 46 digits, `e`, exponent 5 (48 bytes) -/
def bytBs : List Nat := "1234567890123456789012345678901234567890123456e5".toList.map Char.toNat

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the synthetic contents of the memory outside the binary's data -/
def val (a : Nat) : Nat :=
  if TW ≤ a ∧ a < TW + 48 then (if a = TW then 8 else if a = TW + 20 then 8 else 0)
  else if a = 0x100001 then 0x10
  else if 0x210000 ≤ a ∧ a < 0x210008 then nb gW 0x210000 a
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
  else if 0x5b7c50 ≤ a ∧ a < 0x5b7c60 then (if a = 0x5b7c50 ∨ a = 0x5b7c58 then 1 else 0)
  else if 0x5b7ba0 ≤ a ∧ a < 0x5b7bb0 then (if a = 0x5b7ba0 ∨ a = 0x5b7ba8 then 1 else 0)
  else if 0x5b8588 ≤ a ∧ a < 0x5b85a8 then nb (multW + 32 * ((a - 0x5b8580) / 8 - 1)) 0 ((a - 0x5b8580) % 8)
  else if multW ≤ a ∧ a < multW + 128 then nb (10 ^ (19 * ((a - multW) / 32 + 1))) 0 ((a - multW) % 32)
  else 0

def byteAt (a : Nat) : Nat :=
  match Janus.dataSegByte Extracted.program.data a with
  | some n => n
  | none => val a

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (byteAt a),
   (Extracted.program.data.map fun d => (⟨d.base, d.bytes.length, false⟩ : Region)) ++
   [⟨TW, 48, false⟩, ⟨loW, 0x4000, true⟩, ⟨gW, 0x100, false⟩, ⟨0x210000, 8, false⟩,
    ⟨zW, 32, true⟩, ⟨strW, 0x1000, false⟩, ⟨hdrW, 16, false⟩, ⟨str2W, 0x1000, false⟩, ⟨hdr2W, 16, false⟩,
    ⟨slW, 24, false⟩, ⟨bufW, 0x1000, false⟩, ⟨BUMP, 0x1000, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0x5b7c50, 16, false⟩, ⟨0x5b7ba0, 16, false⟩, ⟨0x5b7ef0, 16, false⟩, ⟨0x5def20, 4, false⟩, ⟨0x5b8580, 40, false⟩,
    ⟨multW, 128, false⟩, ⟨0x5df444, 1, false⟩, ⟨0x4f6000, 0x2000, false⟩]⟩

def tyS : Nat := janus_eval% Extracted.dataAddr.«type:string#f88732b8»
def tyB : Nat := janus_eval% Extracted.dataAddr.«type:[]uint8#7efbbf65»
def tyU : Nat := janus_eval% Extracted.dataAddr.«type:uint8#6a8c7679»
def itabE : Nat := janus_eval% Extracted.dataAddr.«go:itab.*errors.errorString,error»
def stW : Nat := janus_eval% Extracted.dataAddr.«runtime.staticuint64s»

def zV : BitVec 64 := BitVec.ofNat 64 zW
def dwS : BitVec 64 := BitVec.ofNat 64 hdrW
def dwS2 : BitVec 64 := BitVec.ofNat 64 hdr2W
def dwB : BitVec 64 := BitVec.ofNat 64 slW

/-- the call state: receiver `zV`, type word `tw`, data word `dw` -/
def st (tw dw : BitVec 64) : State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then tw else if i = 1 then dw
      else if i = 4 then BitVec.ofNat 64 spW else if i = 14 then BitVec.ofNat 64 gW else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    fsBase := BitVec.ofNat 64 fsW, mem := mem0 }

theorem cfg_lit : cfg = (0x5b7c50, 0x5b7ba0, 0x5b8580, 0x4d78a0, 0x4f1a00, 0x4f19e0, 0x4f09f0, 0x5b7ef0, 0x5def20,
    0x4e6568, 0x4ef9b4, mgA, mvA, newA, w1A, w2A) := by
  rfl


theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

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
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem data_small : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0x500000 := by decide

theorem dsb_none (a : Nat) (h : 0x500000 ≤ a) : Janus.dataSegByte Extracted.program.data a = none := by
  unfold Janus.dataSegByte
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have := data_small d hd
  simp only [ite_eq_right_iff]
  intro h2; omega

theorem val_big (a : Nat) (h : 0x600000 ≤ a) : val a = 0 := by
  simp only [val, multW, strW, hdrW, str2W, hdr2W, slW, bufW, gW, TW]
  simp (disch := omega) only [if_neg]
  exact if_neg (by omega)

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (byteAt i) = 0
  have : 0x600000 ≤ i := by simp only [HEAP] at h; omega
  simp only [byteAt, dsb_none i (by omega), val_big i this]; rfl

theorem inv0 (tw dw : BitVec 64) : R.inv 0x400 [] ((st tw dw).regs 14).toNat (view R.rt [] (st tw dw).mem) := by
  refine toyInv_init (m := mem0) (g := ((st tw dw).regs 14).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)


theorem static_b : StaticOK cfg (R3 TW) TW mem0 := by
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

theorem maxdig0 : ∀ k, k < 78 → mem0.readLE (0x4ef9b4 + k) 1 = Fv256.I.maxDigit k := by
  decide

def twS : BitVec 64 := BitVec.ofNat 64 tyS
def twB : BitVec 64 := BitVec.ofNat 64 tyB
def twU : BitVec 64 := BitVec.ofNat 64 tyU
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
  rw [cfg_lit]
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
  have e : cfg = _ := cfg_lit
  rw [e] at hc ⊢
  unfold TopPre0
  refine ⟨by simp [viewS, setRegF_apply, st], by simp [viewS, setRegF_apply], by simp [viewS, setRegF_apply],
    ?_, ?_, by decide, by decide, ?_, by decide, ?_, by decide, ?_, by decide, ?_, ?_, hm, ⟨by decide, by decide⟩,
    by decide, ?_, ?_, ?_, ?_, ⟨by decide, Or.inr (by decide)⟩, by decide, by decide, hc⟩
  · have := mod0; rw [cfg_lit] at this; exact this
  · have := env0 twS dwS; rw [cfg_lit] at this; exact this
  · have := mult0; rw [cfg_lit] at this; exact this
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide


theorem initDone0 : Fv256.Amd64.FromDecimalSpec.InitDone cfg (R3 TW) mem0 := by
  rw [cfg_lit]
  exact ⟨by decide, by decide, by decide, by decide, fun r hr => by simp only [R3_priv, List.mem_singleton] at hr; subst hr; simp⟩

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by rw [linked_eq]; decide)

theorem setup (tw dw : BitVec 64) :
    CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, tw, dw] (st tw dw) :=
  ⟨rfl, by show mem0.readLE (BitVec.ofNat 64 spW).toNat 8 = retW; decide, rfl,
    by show 3 ≤ numIntRegs; decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl, rfl⟩

theorem tls0 (tw dw : BitVec 64) : TlsG (st tw dw) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show 8 ≤ (BitVec.ofNat 64 fsW).toNat; decide
  · show (BitVec.ofNat 64 fsW).toNat ≤ 2 ^ 48; decide
  · show mem0.accessible ((BitVec.ofNat 64 fsW).toNat - 8) 8 false = true; decide
  · show mem0.readLE ((BitVec.ofNat 64 fsW).toNat - 8) 8 = (BitVec.ofNat 64 gW).toNat; decide

theorem dataLoaded0 : Extracted.program.DataLoaded mem0 := by
  refine Janus.Amd64.Program.DataLoaded_of_dataSegByte (by unfold Janus.DataSegsDisjoint; decide) (fun d hd => ?_) (by decide) (fun a n h => ?_)
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

theorem preS : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twS dwS (st twS dwS) := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, Or.inr (Or.inl ⟨by decide, ⟨by decide, by decide⟩, ?_, by decide, ⟨tls0 twS dwS, ?_, initDone0⟩, ?_, ?_⟩)⟩
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [hdrP_S, hdrN_S]; exact top0S
  · rw [hdrP_S, hdrN_S]; exact pageS

def pSV2 : BitVec 64 := BitVec.ofNat 64 str2W
def nSV2 : BitVec 64 := BitVec.ofNat 64 strBs2.length

theorem hdrP_N : hdrP (st twS dwS2) dwS2 = pSV2 := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrP pSV2; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE hdr2W 8) % 2 ^ 64 = str2W % 2 ^ 64
  have : mem0.readLE hdr2W 8 = str2W := by decide
  rw [this]

theorem hdrN_N : hdrN (st twS dwS2) dwS2 = nSV2 := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrN nSV2; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE (hdr2W + 8) 8) % 2 ^ 64 = strBs2.length % 2 ^ 64
  have : mem0.readLE (hdr2W + 8) 8 = strBs2.length := by decide
  rw [this]



theorem chunk_dummy : True := trivial
theorem chunkN : ChunkAll cfg R (R3 TW) [] 0x400 pSV2.toNat nSV2.toNat loW hiW mem0 := by
  intro sp sl h1 h2 h3 h4
  have e1 : pSV2.toNat = str2W := by decide
  have e2 : nSV2.toNat = strBs2.length := by decide
  have e3 : strBs2.length = 13 := by decide
  simp only [e1, e2, e3, str2W] at h1 h2
  have hsp : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  have hsl : (BitVec.ofNat 64 sl).toNat = sl := Nat.mod_eq_of_lt (by omega)
  have hacc : mem0.accessible str2W 13 false = true := by decide
  rw [cfg_lit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsl]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h3, h4, rfl⟩)))
  · intro q; simp only [hsl, hsp]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, sp, sl, h3, h4, rfl⟩))))
  · simp only [hsl]; exact Nat.le_trans (chunk_bs sl h4) (Nat.le_refl _)
  · simp only [hsp, hsl]; exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by simp only [str2W]; omega) (by simp only [str2W]; omega)
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


theorem top0N : TopPre0 cfg R (R3 TW) TW 0x400 [] loW hiW zV pSV2 nSV2 (viewS (st twS dwS2) pSV2 nSV2) := by
  have hm := maxdig0
  have hc := chunkN
  have e : cfg = _ := cfg_lit
  rw [e] at hc ⊢
  unfold TopPre0
  refine ⟨by simp [viewS, setRegF_apply, st], by simp [viewS, setRegF_apply], by simp [viewS, setRegF_apply],
    ?_, ?_, by decide, by decide, ?_, by decide, ?_, by decide, ?_, by decide, ?_, ?_, hm, ⟨by decide, by decide⟩,
    by decide, ?_, ?_, ?_, ?_, ⟨by decide, Or.inr (by decide)⟩, by decide, by decide, hc⟩
  · have := mod0; rw [cfg_lit] at this; exact this
  · have := env0 twS dwS2; rw [cfg_lit] at this; exact this
  · have := mult0; rw [cfg_lit] at this; exact this
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide


theorem pageN : Fv256.IndexByte.PageReadable mem0 pSV2.toNat nSV2.toNat := by
  unfold Fv256.IndexByte.PageReadable
  right
  exact ⟨by decide, by decide⟩

theorem preN : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twS dwS2 (st twS dwS2) := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, Or.inr (Or.inl ⟨by decide, ⟨by decide, by decide⟩, ?_, by decide, ⟨tls0 twS dwS2, ?_, initDone0⟩, ?_, ?_⟩)⟩
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [hdrP_N, hdrN_N]; exact top0N
  · rw [hdrP_N, hdrN_N]; exact pageN



def pBV : BitVec 64 := BitVec.ofNat 64 bufW
def nBV : BitVec 64 := 48#64

theorem preNil : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV 0#64 0#64 (st 0#64 0#64) := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, Or.inl ⟨rfl, ⟨by decide, by decide⟩, Or.inr (by decide), by decide, by decide, by decide, by decide, by decide⟩⟩

theorem preOther : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twU 0#64 (st twU 0#64) := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, Or.inr (Or.inr (Or.inr ⟨by decide, by decide, by decide, by decide, ?_, ?_,
    mod0, env0 twU 0#64, ?_, by decide, ?_, by decide⟩))⟩
  · apply outside_of_decide; decide
  · intro r hr
    rw [rt_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · exact Or.inl ⟨rfl, Or.inr rfl⟩
  · rw [rt_eq]; apply outside_of_decide; decide


theorem hdrP_B : hdrP (st twB dwB) dwB = pBV := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrP pBV; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE slW 8) % 2 ^ 64 = bufW % 2 ^ 64
  have : mem0.readLE slW 8 = bufW := by decide
  rw [this]

theorem hdrN_B : hdrN (st twB dwB) dwB = nBV := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrN nBV; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE (slW + 8) 8) % 2 ^ 64 = 48 % 2 ^ 64
  have : mem0.readLE (slW + 8) 8 = 48 := by decide
  rw [this]

theorem preB0 : PreB cfg sbAddr stAddr R (R3 TW) TW 0x400 [] loW hiW zV pBV nBV (viewS (st twB dwB) pBV nBV) := by
  have hm := maxdig0
  unfold PreB
  refine ⟨?r0, ?r3, ?r1, ?mod, ?env, ?lo4, ?hi4, ?okD, ?cost, ?stWin, ?stRt, ?stPriv, ?stZ, ?mult, ?multRt, ?multK, ?eofA, ?eofW, ?eofR,
    ?bigA, ?bigW, ?bigR, ?init, ?maxA, ?maxW, ?maxR, ?maxB, ?zbuf, ?zwin, ?zR, ?zP, ?zS, ?zg, ?ibuf, ?iwin, ?chunk⟩
  case r0 => simp [viewS, setRegF_apply, st]
  case r3 => simp [viewS, setRegF_apply]
  case r1 => simp [viewS, setRegF_apply]
  case mod => exact mod0
  case env => exact env0 twB dwB
  case init => exact initDone0
  case mult => exact mult0
  case maxB => rw [cfg_lit]; exact hm
  case okD => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, _, pBV.toNat, rfl⟩))))
  all_goals first | decide | (apply outside_of_decide; decide) | (rw [rt_eq]; apply outside_of_decide; decide) | (simp only [R3_priv]; apply outside_of_decide; decide) | skip
  case multK =>
    intro k h1 h2
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rw [cfg_lit, rt_eq]
    rcases hk with rfl | rfl | rfl | rfl <;> (apply outside_of_decide; decide)
  case zbuf => exact ⟨by decide, by decide⟩
  case zR => left; rw [rt_eq]; apply outside_of_decide; decide
  case zS =>
    intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  case ibuf => exact ⟨by decide, by decide⟩
  case chunk =>
    intro sl h1 h2 h3
    have hn : nBV.toNat = 48 := by decide
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h1, h2, rfl⟩))),
      fun q p => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, p, sl, h1, h2, rfl⟩)))), ?_⟩
    have : blockSize sl true + blockSize 48 false ≤ 0x400 - 48 := by
      have h19 : ∀ sl, sl ≤ 19 → blockSize sl true + blockSize 48 false ≤ 0x400 - 48 := by decide
      exact h19 sl h2
    have h48 : roundupsize 48 true = 48 := by decide
    rw [hn, h48]; exact this

theorem pagesB0 : PagesB R stAddr loW hiW mem0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Fv256.IndexByte.PageReadable; right; exact ⟨by decide, by decide⟩
  · intro r hr
    rw [rt_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    unfold Fv256.IndexByte.PageReadable
    rcases hr with rfl | rfl | rfl <;> (right; exact ⟨by decide, by decide⟩)
  · unfold Fv256.IndexByte.PageReadable; right; exact ⟨by decide, by decide⟩

theorem preByt : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twB dwB (st twB dwB) := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, Or.inr (Or.inr (Or.inl ⟨by decide, ⟨by decide, by decide⟩, ?_, ?_, by decide,
    ⟨tls0 twB dwB, ?_, initDone0, ?_⟩, ?_, pagesB0⟩))⟩
  · apply outside_of_decide; decide
  · intro r hr
    rw [rt_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · rw [hdrP_B, hdrN_B]; exact preB0


/-- the contracts of `Scan.correctness` hold of the stub runtime -/
theorem contracts_ok :
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.ifaceeq") (R3 TW) ∧
    NewobjectLiveContract64 (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract64 (Extracted.program.link implA) (Extracted.program.contractAddr "runtime.slicebytetostring") 4096 R
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link implA)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 :=
  ⟨by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_sb]; exact model_sb, by rw [addr_cm]; exact hcmp⟩

end Fv256.Amd64.Scan.Witness
