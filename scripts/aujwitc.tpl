import Extracted
import Fv256.Amd64.UnmarshalTextS0
import Fv256.Amd64.UnmarshalSpec
import Fv256.Amd64.UnmarshalHex
import Fv256.Amd64.UnmarshalQ
import Fv256.Amd64.AUjWitB

/-!
# Witness for `UnmarshalText` / `UnmarshalJSON` (amd64), part C: the concrete call states

`UnmarshalText(z, "777…7")` (48 digits) and the `0x…` hex input, in the toy runtime `R` with the interface model `R0`, a stack window
`[lo, hi)` and a memory laid out by hand (`mem0`: model metadata, heap, the binary's static objects the proof reads at the
extraction's own addresses with synthetic contents, the multiplier objects, hex table, error variables, `z`, the inputs).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib Fv256.Amd64.UnmarshalQ

namespace Fv256.Amd64.UjWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.IfaceModel

abbrev cfg : SfdCfg := Fv256.Amd64.UnmarshalTextS.cfg

def spW : Nat := 0x100000
def loW : Nat := 0xFC000
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def zW : Nat := 0x300000
def multW : Nat := 0x501000
def bW : Nat := 0x20000

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the synthetic contents of `mem0` (every branch is flat: a single comparison, a single value) -/
def val (a : Nat) : Nat :=
  if 0x10000 ≤ a ∧ a < 0x11000 then (IfaceModel.wmem.bytes a).toNat
  else if a = 0x400003 then 0x10
  else if a = 0x100001 then 0x10
  else if 0x301000 ≤ a ∧ a < 0x301000 + 48 then 0x37
  else if a = 0x303000 then 0x22
  else if a = 0x303031 then 0x22
  else if 0x303001 ≤ a ∧ a < 0x303031 then 0x37
  else if a = 0x302000 then 48
  else if a = 0x302001 then 120
  else if 0x302002 ≤ a ∧ a < 0x302000 + 48 then 0x31
  else if a = 0x4d78a0 then 48
  else if a = 0x4d78a8 then 1
  else if a = 0x4f19ea then 1
  else if 0x4ef9b4 ≤ a ∧ a < 0x4ef9b4 + 78 then Fv256.I.maxDigit (a - 0x4ef9b4)
  else if 0x5b8588 ≤ a ∧ a < 0x5b85a8 then nb (0x501000 + 32 * ((a - 0x5b8580) / 8 - 1)) 0 ((a - 0x5b8580) % 8)
  else if 0x501000 ≤ a ∧ a < 0x501000 + 128 then nb (10 ^ (19 * ((a - 0x501000) / 32 + 1))) 0 ((a - 0x501000) % 32)
  else if 5176782 ≤ a ∧ a < 5176782 + 256 then (hexNib (a - 5176782)).getD 255
  else if 5995344 ≤ a ∧ a < 5995344 + 96 then (if (a - 5995344) % 8 = 0 then 1 else 0)
  else if a = 0x5b7c50 then 1
  else if a = 0x5b7c58 then 1
  else 0

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (val a),
   [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨loW, hiW - loW, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩,
    ⟨0x301000, 48, false⟩, ⟨0x302000, 48, false⟩, ⟨0x303000, 50, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0x4d78a0, 16, false⟩, ⟨0x4ef9b4, 78, false⟩, ⟨0x4f09f0, 8, false⟩, ⟨0x4f19e0, 32, false⟩, ⟨0x5b7ba0, 16, false⟩,
    ⟨0x5b7c50, 16, false⟩, ⟨0x5b7ef0, 16, false⟩, ⟨0x5b8580, 40, false⟩, ⟨0x5def20, 4, false⟩, ⟨multW, 128, false⟩,
    ⟨5176782, 256, false⟩, ⟨5995344, 96, false⟩]⟩

def zV : BitVec 64 := BitVec.ofNat 64 zW
def pV : BitVec 64 := BitVec.ofNat 64 0x301000
def pHV : BitVec 64 := BitVec.ofNat 64 0x302000
def nV : BitVec 64 := 48#64
def retW : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then pV else if i = 1 then nV else if i = 7 then nV
      else if i = 4 then BitVec.ofNat 64 spW else if i = 14 then BitVec.ofNat 64 gW else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem cfg_lit : cfg = (0x5b7c50, 0x5b7ba0, 0x5b8580, 0x4d78a0, 0x4f1a00, 0x4f19e0, 0x4f09f0, 0x5b7ef0, 0x5def20,
    0x4e6568, 0x4ef9b4, mgA, mvA, newA, w1A, w2A) := by
  rfl

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem outside_of_decide {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L :=
  Janus.Contracts.outside_of_forall h

theorem mod0 : Mod cfg R R0 TD [] := by
  rw [cfg_lit]
  refine ⟨R0_laws, by decide, Or.inl rfl, ?_, fun r hr => absurd hr (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  simp only [val]
  repeat rw [if_neg (by omega)]
  try exact if_neg (by omega)

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (val i) = 0
  rw [val_big i (by simp only [HEAP] at h; omega)]; rfl

theorem inv0 : R.inv bW [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)

theorem static0 : StaticOK cfg R0 TD s0.mem := by
  rw [cfg_lit]
  exact ⟨by decide, Or.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env0 : Env cfg R R0 TD bW [] loW hiW s0 := by
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

theorem mult0 : MultOK cfg zV.toNat loW hiW s0.mem := by
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
  intro k hk
  show (BitVec.ofNat 8 (val (0x4ef9b4 + k))).toNat = _
  have h1 : val (0x4ef9b4 + k) = Fv256.I.maxDigit k := by
    simp only [val]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    rw [Nat.add_sub_cancel_left]
  have h2 : Fv256.I.maxDigit k < 256 := by
    unfold Fv256.I.maxDigit
    have := Nat.mod_lt ((2 ^ 256 - 1) / 10 ^ (77 - k)) (by decide : 0 < 10)
    omega
  rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h2

theorem init0 : Fv256.Amd64.FromDecimalSpec.InitDone cfg R0 s0.mem := by
  rw [cfg_lit]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro r hr
  simp only [R0_priv, List.mem_singleton] at hr
  subst hr; decide

theorem hrt48 : Outside 0x301000 48 R.rt := by rw [rt_eq]; apply outside_of_decide; decide
theorem hpr48 : Outside 0x301000 48 R0.priv := by simp only [R0_priv]; apply outside_of_decide; decide
theorem hacc48 : s0.mem.accessible 0x301000 48 false = true := by decide

theorem chunk0 : ∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nV.toNat → R.ok cfg.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok cfg.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ bW - roundupsize nV.toNat true := by
  rw [cfg_lit]
  intro sl h1 h2 h3
  have hr : roundupsize nV.toNat true = 48 := by decide
  have a1 := Janus.Contracts.blockSize_le_maxSmallSize sl true (by simp only [Janus.Contracts.maxSmallSize]; omega)
  have a2 : blockSize 48 false ≤ 32768 := by decide
  have a3 : (32768 : Nat) = Janus.Contracts.maxSmallSize := rfl
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h1, h2, rfl⟩))),
    fun q p => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, p, sl, rfl, h1, h2⟩)))), ?_⟩
  rw [hr]; simp only [bW]; omega

theorem pre0 : PreU0 cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R0 TD bW []
    loW hiW zV pV nV s0 := by
  have hm := maxdig0
  have hc := init0
  have hk := chunk0
  have e1 : Fv256.Amd64.UnmarshalTextS.sbAddr = sbA := by decide
  rw [e1]
  have hu : Fv256.Amd64.UnmarshalTextS.stAddr = 5205472 := by decide
  rw [hu]
  unfold PreU0
  refine ⟨rfl, rfl, rfl, mod0, env0, by decide, by decide, ?_, ?_, by decide, ?_, ?_, ?_, ?_, mult0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hc, ?_, ?_, ?_, hm, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ⟨by decide, by decide⟩, ?_, hk⟩
  all_goals first
    | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 72, 0x301000, by decide, Or.inl rfl⟩)))))
    | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 40, 0x301000, by decide, Or.inl rfl⟩)))))
    | decide
    | (rw [cfg_lit]; decide)
    | (apply outside_of_decide; decide)
    | (rw [rt_eq]; apply outside_of_decide; decide)
    | (simp only [R0_priv]; apply outside_of_decide; decide)
    | (intro k h1 h2
       rw [cfg_lit, rt_eq]
       have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
       rcases hk with rfl | rfl | rfl | rfl <;> (apply outside_of_decide; decide))
    | (left; rw [rt_eq]; apply outside_of_decide; decide)
    | (intro r hr
       simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
       apply outside_of_decide
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by rw [linked_eq]; decide)

theorem setup : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pV, nV, nV] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

theorem hexEnv0 : HexEnv R loW hiW zV s0 := by
  refine ⟨?_, by decide, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · intro c hc
    show (BitVec.ofNat 8 (val (5176782 + c))).toNat = _
    have h1 : val (5176782 + c) = (hexNib c).getD 255 := by
      simp only [val]
      repeat rw [if_neg (by omega)]
      rw [if_pos (by omega)]
      rw [Nat.add_sub_cancel_left]
    rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.C.hexNib_getD_lt c)
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · intro e he
    have hk : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [errAddrOf]; decide)


def pQV : BitVec 64 := BitVec.ofNat 64 0x303000
def nQ : BitVec 64 := 50#64

/-- the quoted call state: the input is `"` + 48 digits + `"` at `0x303000` -/
def s2 : State := { s0 with regs := fun i => if i = 3 then pQV else if i = 1 then nQ else if i = 7 then nQ else s0.regs i }

theorem chunk2 : ∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nQ.toNat → R.ok cfg.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok cfg.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ bW - roundupsize nQ.toNat true := by
  rw [cfg_lit]
  intro sl h1 h2 h3
  have hr : roundupsize nQ.toNat true = 64 := by decide
  have a1 := Janus.Contracts.blockSize_le_maxSmallSize sl true (by simp only [Janus.Contracts.maxSmallSize]; omega)
  have a2 : blockSize 48 false ≤ 32768 := by decide
  have a3 : (32768 : Nat) = Janus.Contracts.maxSmallSize := rfl
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h1, h2, rfl⟩))),
    fun q p => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, p, sl, rfl, h1, h2⟩)))), ?_⟩
  rw [hr]; simp only [bW]; omega

theorem pre2m : PreU0m cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R0 TD bW []
    loW hiW zV pQV nQ s2 := by
  have hm := maxdig0
  have hc := init0
  have hk := chunk2
  have hu : Fv256.Amd64.UnmarshalTextS.stAddr = 5205472 := by decide
  rw [hu]
  unfold PreU0m
  refine ⟨rfl, rfl, rfl, mod0, env0, by decide, by decide, by decide, ?_, ?_, ?_, ?_, mult0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hc, ?_, ?_, ?_, hm, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ⟨by decide, by decide⟩, ?_, hk⟩
  all_goals first
    | decide
    | (rw [cfg_lit]; decide)
    | (apply outside_of_decide; decide)
    | (rw [rt_eq]; apply outside_of_decide; decide)
    | (simp only [R0_priv]; apply outside_of_decide; decide)
    | (intro k h1 h2
       rw [cfg_lit, rt_eq]
       have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
       rcases hk with rfl | rfl | rfl | rfl <;> (apply outside_of_decide; decide))
    | (left; rw [rt_eq]; apply outside_of_decide; decide)
    | (intro r hr
       simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
       apply outside_of_decide
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem setup2 : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pQV, nQ, nQ] s2 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

theorem quoted2 : Quoted s2.mem pQV.toNat nQ.toNat := ⟨by decide, by decide, by decide⟩
theorem unq0 : ¬ Quoted s0.mem pV.toNat nV.toNat := by unfold Quoted; decide

theorem okq2 : QPre cfg Fv256.Amd64.UnmarshalTextS.sbAddr R bW loW pQV nQ s2 := by
  have e1 : Fv256.Amd64.UnmarshalTextS.sbAddr = sbA := by decide
  rw [e1]
  refine ⟨by decide, ?_, ?_, by decide, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 152, 0x303001, by decide, Or.inr rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 120, 0x303001, by decide, Or.inr rfl⟩))))
  · intro sl h1 h2 h3
    have e1 : nQ.toNat = 50 := by decide
    have e2 : nV.toNat = 48 := by decide
    have h3' : sl ≤ nV.toNat := by rw [e1] at h3; omega
    have := chunk0 sl h1 h2 h3'
    have hr : roundupsize (nQ.toNat - 2) true = roundupsize nV.toNat true := by decide
    rw [hr]; exact this

def UJPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI : BitVec 64) (s : State) : Prop :=
  ((PreU0m cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
      (¬ Quoted s.mem pI.toNat nI.toNat → OkOut Fv256.Amd64.UnmarshalTextS.sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧
    (Quoted s.mem pI.toNat nI.toNat → QPre cfg Fv256.Amd64.UnmarshalTextS.sbAddr R b lo pI nI s)

theorem preQ : UJPre R R0 TD bW [] loW hiW zV pQV nQ s2 :=
  ⟨⟨⟨pre2m, fun h => absurd quoted2 h⟩, hexEnv0⟩, fun _ => okq2⟩

theorem preU : UJPre R R0 TD bW [] loW hiW zV pV nV s0 :=
  ⟨⟨⟨pre0.toM cfg, fun _ => pre0.okOut cfg⟩, hexEnv0⟩, fun h => absurd h unq0⟩



theorem nonvacuous_core : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract64 (Extracted.program.link impl) Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    (((PreU0m cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
        (¬ Quoted s.mem pI.toNat nI.toNat → OkOut Fv256.Amd64.UnmarshalTextS.sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧
      (Quoted s.mem pI.toNat nI.toNat → QPre cfg Fv256.Amd64.UnmarshalTextS.sbAddr R b lo pI nI s)) :=
  ⟨implA, R, R0, TD, bW, [], loW, hiW, zV, pQV, nQ, nQ, retW, s2,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, by rw [show Fv256.Amd64.UnmarshalTextS.sbAddr = sbA by decide]; exact model_sb,
    hret, setup2, preQ⟩


theorem unq_core : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract64 (Extracted.program.link impl) Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    (((PreU0m cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
        (¬ Quoted s.mem pI.toNat nI.toNat → OkOut Fv256.Amd64.UnmarshalTextS.sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧
      (Quoted s.mem pI.toNat nI.toNat → QPre cfg Fv256.Amd64.UnmarshalTextS.sbAddr R b lo pI nI s)) :=
  ⟨implA, R, R0, TD, bW, [], loW, hiW, zV, pV, nV, nV, retW, s0,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, by rw [show Fv256.Amd64.UnmarshalTextS.sbAddr = sbA by decide]; exact model_sb,
    hret, setup, preU⟩

end Fv256.Amd64.UjWit
