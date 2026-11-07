import Extracted
import Fv256.Arm64.UnmarshalJSONHead
import Fv256.Arm64.UnmarshalSpecJ
import Fv256.Arm64.UnmarshalJSONWitB

/-!
# Witness for `UnmarshalJSON` (arm64), part C: a concrete call state

`UnmarshalText(z, "777…7")` (48 digits) with the toy runtime `R`, the interface model `R0`, a stack window `[lo, hi)`, and a memory laid
out by hand (`mem0`): the model's metadata, the heap, the binary's static objects the proof reads (at the extraction's own addresses, with
synthetic contents), the four multiplier objects `10^(19 k)`, `z`, the input string, the hex digit table and the six hex error variables.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalSpecJ

namespace Fv256.Arm64.UnmarshalJSONWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.IfaceModel

def spW : Nat := 0x100000
def loW : Nat := 0xFE000
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def zW : Nat := 0x300000

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the synthetic contents of `mem0` -/
def val (a : Nat) : Nat :=
  if 0x10000 ≤ a ∧ a < 0x11000 then (IfaceModel.wmem.bytes a).toNat
  else if a = 0x400003 then 0x10
  else if a = 0x301000 ∨ a = 0x301000 + 49 then 0x22
  else if 0x301000 ≤ a ∧ a < 0x301000 + 50 then 0x37
  else if 0x302000 ≤ a ∧ a < 0x302000 + 48 then 0x37
  else if a = 0xdc840 then 48
  else if a = 0xdc848 then 1
  else if a = 0xf692a then 1
  else if 0xf490b ≤ a ∧ a < 0xf490b + 78 then Fv256.I.maxDigit (a - 0xf490b)
  else if 0x1b6548 ≤ a ∧ a < 0x1b6568 then nb (0x501000 + 32 * ((a - 0x1b6540) / 8 - 1)) 0 ((a - 0x1b6540) % 8)
  else if 0x501000 ≤ a ∧ a < 0x501000 + 128 then nb (10 ^ (19 * ((a - 0x501000) / 32 + 1))) 0 ((a - 0x501000) % 32)
  else if 1002789 ≤ a ∧ a < 1002789 + 256 then (hexNib (a - 1002789)).getD 255
  else if 1792784 ≤ a ∧ a < 1792784 + 96 then (if (a - 1792784) % 8 = 0 then 1 else 0)
  else if a = 0x1b5c10 ∨ a = 0x1b5c18 ∨ a = 0x1b5b60 ∨ a = 0x1b5b68 then 1
  else 0

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (val a),
   [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨loW, hiW - loW, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩,
    ⟨0x301000, 50, false⟩, ⟨0x302000, 48, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0xdc840, 16, false⟩, ⟨0xf490b, 78, false⟩, ⟨0xf5940, 8, false⟩, ⟨0xf6920, 16, false⟩, ⟨0x1b5b60, 16, false⟩,
    ⟨0x1b5c10, 16, false⟩, ⟨0x1b5eb0, 16, false⟩, ⟨0x1b6540, 40, false⟩, ⟨0x1e34c0, 4, false⟩, ⟨0x501000, 128, false⟩,
    ⟨1002789, 256, false⟩, ⟨1792784, 96, false⟩]⟩

def zV : BitVec 64 := BitVec.ofNat 64 zW
def pV : BitVec 64 := BitVec.ofNat 64 0x301000
def pHV : BitVec 64 := BitVec.ofNat 64 0x302000
def nV : BitVec 64 := 50#64
def retW : Nat := 0x1000
def bW : Nat := 0x20000

def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 1 then pV else if i = 2 then nV else if i = 3 then nV
      else if i = 28 then BitVec.ofNat 64 gW else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 spW, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem cfg_lit : Fv256.Arm64.UnmarshalJSON.cfg = (SfdCfg.mk 0x1b5c10 0x1b5b60 0x1b6540 0xdc840 0xf6940 0xf6920 0xf5940 0x1b5eb0 0x1e34c0
    0xeb483 0xf490b mgA mvA newA w1A w2A) := by
  rfl

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl


theorem hT_R0 (m : Memory) (g : BitVec 64) (h : R0.Env m g) :
    isRegularMemory m TD = true ∧ isDirectIface m TD = false ∧ tySize m TD = 8 := by
  obtain ⟨-, -, d1, -, d3, -, -, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [isRegularMemory, tyTFlag, d3]; decide
  · simp only [isDirectIface, tyTFlag, d3]; decide
  · simp only [tySize, d1]

theorem outside_of_decide {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L :=
  Janus.Contracts.outside_of_forall h

theorem mod0 : Mod Fv256.Arm64.UnmarshalJSON.cfg R R0 TD [] := by
  rw [cfg_lit]
  refine ⟨R0_laws, by decide, by decide, Or.inl rfl, ?_, fun r hr => absurd hr (by simp), ?_, ?_, ?_, ?_, ?_, ?_, hT_R0⟩
  · intro r hr
    rw [rt_eq]
    simp only [R0_priv, List.mem_singleton] at hr
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
    simp only [R0_priv]
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | decide
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))


theorem val_big (a : Nat) (h : 0x600000 ≤ a) : val a = 0 := by
  unfold val
  repeat rw [if_neg (by omega)]

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (val i) = 0
  rw [val_big i (by simp only [HEAP] at h; omega)]; rfl

theorem inv0 : R.inv bW [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)

theorem static0 : StaticOK Fv256.Arm64.UnmarshalJSON.cfg R0 TD s0.mem := by
  rw [cfg_lit]
  exact ⟨by decide, Or.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env0 : Env Fv256.Arm64.UnmarshalJSON.cfg R R0 TD bW [] loW hiW s0 := by
  rw [cfg_lit]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_,
    by decide, ?_, static0, ?_, inv0, fun r hr => absurd hr (by simp)⟩
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact ⟨by decide, by decide, by unfold Desc; decide⟩

theorem mult0 : MultOK Fv256.Arm64.UnmarshalJSON.cfg zV.toNat loW hiW s0.mem := by
  rw [cfg_lit]
  refine ⟨by decide, ?_, ?_⟩
  · apply outside_of_decide; decide
  · intro k h1 h2
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    all_goals refine ⟨by decide, by decide, by decide, ?_⟩
    all_goals (apply outside_of_decide; decide)

theorem maxdig0 : ∀ k, k < 78 → s0.mem.readLE (Fv256.Arm64.UnmarshalJSON.cfg.maxStr + k) 1 = Fv256.I.maxDigit k := by
  rw [cfg_lit]
  intro k hk
  show (BitVec.ofNat 8 (val (0xf490b + k))).toNat = _
  have h1 : val (0xf490b + k) = Fv256.I.maxDigit k := by
    unfold val
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [Nat.add_sub_cancel_left]
  have h2 : Fv256.I.maxDigit k < 256 := by
    unfold Fv256.I.maxDigit
    have := Nat.mod_lt ((2 ^ 256 - 1) / 10 ^ (77 - k)) (by decide : 0 < 10)
    omega
  rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h2



theorem init0 : Fv256.Arm64.UnmarshalSpec.InitDone Fv256.Arm64.UnmarshalJSON.cfg R0 s0.mem := by
  rw [cfg_lit]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro r hr
  simp only [R0_priv, List.mem_singleton] at hr
  subst hr; decide

theorem hrt50 : Outside 0x301000 50 R.rt := by rw [rt_eq]; apply outside_of_decide; decide
theorem hpr50 : Outside 0x301000 50 R0.priv := by simp only [R0_priv]; apply outside_of_decide; decide
theorem hacc50 : s0.mem.accessible 0x301000 50 false = true := by decide

theorem chunk_gen (n : Nat) (hn : roundupsize n true ≤ bW) (hb : roundupsize n true = 48 ∨ roundupsize n true = 64) :
    ∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ n → R.ok Fv256.Arm64.UnmarshalJSON.cfg.mallocgc [sl, 0, 0] ∧
      (∀ q p, R.ok Fv256.Arm64.UnmarshalJSON.cfg.memmove [q, p, sl]) ∧ blockSize sl true + blockSize 48 false ≤ bW - roundupsize n true := by
  intro sl h1 h2 h3
  have a1 := Janus.Contracts.blockSize_le_maxSmallSize sl true (by simp only [Janus.Contracts.maxSmallSize]; omega)
  have a2 : blockSize 48 false ≤ 32768 := by decide
  have a3 : (32768 : Nat) = Janus.Contracts.maxSmallSize := rfl
  rw [cfg_lit]
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h1, h2, rfl⟩))),
    fun q p => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, p, sl, rfl, h1, h2⟩)))), ?_⟩
  simp only [bW]; rcases hb with hb | hb <;> rw [hb] <;> omega

theorem quoted0 : Quoted s0.mem pV.toNat nV.toNat := by
  unfold Quoted; refine ⟨by decide, by decide, by decide⟩

theorem pre0 : PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R0 TD bW []
    loW hiW zV pV nV s0 := by
  have hm := maxdig0
  have hc := init0
  refine ⟨?_, fun hq => absurd quoted0 hq, fun _ => ⟨by decide, ?_, ?_, by decide, ?_⟩⟩
  · refine ⟨rfl, rfl, rfl, mod0, env0, by decide, by decide, by decide, ?_, ?_, ?_, ?_, mult0, ?_⟩
    · apply outside_of_decide; decide
    · rw [rt_eq]; apply outside_of_decide; decide
    · simp only [R0_priv]; apply outside_of_decide; decide
    · apply outside_of_decide; decide
    rw [cfg_lit] at hm hc ⊢
    refine ⟨?_, ?_, by decide, ?_, ?_, by decide, ?_, ?_, hc, by decide, ?_, ?_, hm, ⟨by decide, by decide⟩, by decide, ?_, ?_, ?_,
      by decide, ⟨by decide, by decide⟩, by decide, ?_⟩
    · rw [rt_eq]; apply outside_of_decide; decide
    · intro k h1 h2
      have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl | rfl | rfl <;> (rw [rt_eq]; apply outside_of_decide; decide)
    · apply outside_of_decide; decide
    · rw [rt_eq]; apply outside_of_decide; decide
    · apply outside_of_decide; decide
    · rw [rt_eq]; apply outside_of_decide; decide
    · apply outside_of_decide; decide
    · rw [rt_eq]; apply outside_of_decide; decide
    · left; rw [rt_eq]; apply outside_of_decide; decide
    · simp only [R0_priv]; apply outside_of_decide; decide
    · intro r hr
      simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      apply outside_of_decide
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · exact chunk_gen 50 (by decide) (Or.inr (by decide))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 152, 0x301000 + 1, by decide, Or.inl rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 120, 0x301000 + 1, by decide, Or.inl rfl⟩))))
  · have : nV.toNat - 2 = 48 := by decide
    rw [this]; exact chunk_gen 48 (by decide) (Or.inl (by decide))

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pV, nV, nV] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem hexEnv0 : HexEnv R loW hiW zV s0 := by
  refine ⟨?_, by decide, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · intro c hc
    show (BitVec.ofNat 8 (val (1002789 + c))).toNat = _
    have h1 : val (1002789 + c) = (hexNib c).getD 255 := by
      unfold val
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [Nat.add_sub_cancel_left]
    rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.C.hexNib_getD_lt c)
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · intro e he
    have hk : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [errAddrOf]; decide)

/-- The statement of the witness theorem `nonvacuous` (spelled out there). -/
theorem nonvacuous_core : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s :=
  ⟨implA, R, R0, TD, bW, [], loW, hiW, zV, pV, nV, nV, retW, s0, implOK,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, by rw [show Fv256.Arm64.UnmarshalJSON.sbAddr = sbA by decide]; exact model_sb,
    hret, setup, pre0, hexEnv0⟩


def nU : BitVec 64 := 48#64

def s1 : State := { s0 with regs := fun i => if i = 1 then pHV else if i = 2 then nU else if i = 3 then nU else s0.regs i }

theorem unq1 : ¬ Quoted s1.mem pHV.toNat 48 := by
  unfold Quoted; decide

theorem pre1 : PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R0 TD bW []
    loW hiW zV pHV nU s1 := by
  have h0 := pre0
  obtain ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26,
    f27, f28, f29, f30, f31, f32, f33, f34, f35⟩, -, -⟩ := h0
  refine ⟨⟨f1, rfl, rfl, f4, f5, f6, f7, by decide, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24,
    f25, f26, f27, f28, f29, f30, f31, f32, ⟨by decide, by decide⟩, by decide, ?_⟩,
    fun _ => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 72, 0x302000, by decide, Or.inr rfl⟩)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 40, 0x302000, by decide, Or.inr rfl⟩))))⟩,
    fun hq => absurd hq unq1⟩
  exact chunk_gen 48 (by decide) (Or.inl (by decide))

theorem setup1 : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pHV, nU, nU] s1 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s1, s0] at h ⊢ <;> omega⟩

/-- as `nonvacuous_core`, with the input an UNQUOTED 48-digit string -/
theorem unquoted_core : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s ∧ ¬ Quoted s.mem pI.toNat nI.toNat :=
  ⟨implA, R, R0, TD, bW, [], loW, hiW, zV, pHV, nU, nU, retW, s1, implOK,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, by rw [show Fv256.Arm64.UnmarshalJSON.sbAddr = sbA by decide]; exact model_sb,
    hret, setup1, pre1, hexEnv0, unq1⟩

end Fv256.Arm64.UnmarshalJSONWit
