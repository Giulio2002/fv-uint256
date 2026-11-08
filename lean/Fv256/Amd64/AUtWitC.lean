import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Amd64.UnmarshalTextS0
import Fv256.Amd64.UnmarshalSpec
import Fv256.Amd64.UnmarshalHex
import Fv256.Amd64.AUtWitB

/-!
# Witness for `UnmarshalText` / `UnmarshalJSON` (amd64), part C: the concrete call states

`UnmarshalText(z, "777…7")` (48 digits) and the `0x…` hex input, in the toy runtime `R` with the interface model `R0`, a stack window
`[lo, hi)` and a memory laid out by hand (`mem0`: model metadata, heap, the binary's static objects the proof reads at the
extraction's own addresses with synthetic contents, the multiplier objects, hex table, error variables, `z`, the inputs).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UtWit

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
    ⟨0x301000, 48, false⟩, ⟨0x302000, 48, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
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
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos (by omega)]
      rw [Nat.add_sub_cancel_left]
    rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.C.hexNib_getD_lt c)
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · intro e he
    have hk : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [errAddrOf]; decide)

open Fv256.CallSites

/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `RIP` at the stub's entry and the stub's argument registers. -/
def csNew : State := { s0 with rip := BitVec.ofNat 64 newA, regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else s0.regs i }
def csW1 : State := { s0 with rip := BitVec.ofNat 64 w1A }
def csW2 : State := { s0 with rip := BitVec.ofNat 64 w2A }
def csMg : State := { s0 with rip := BitVec.ofNat 64 mgA, regs := fun i => if i = 0 then 1 else if i = 3 then 0 else if i = 1 then 0 else s0.regs i }
def csMv : State := { s0 with rip := BitVec.ofNat 64 mvA, regs := fun i => if i = 0 then BitVec.ofNat 64 zW else if i = 3 then BitVec.ofNat 64 0x301000 else if i = 1 then 1 else s0.regs i }
def csCm : State := { s0 with rip := BitVec.ofNat 64 cmA, regs := fun i => if i = 0 then 0 else if i = 3 then 0 else if i = 1 then 0 else if i = 7 then 0 else s0.regs i }
def csIf : State := { s0 with rip := BitVec.ofNat 64 ifA, regs := fun i => if i = 0 then 0 else s0.regs i }
def csSb : State := { s0 with rip := BitVec.ofNat 64 sbA, regs := fun i => if i = 0 then BitVec.ofNat 64 0 else if i = 3 then BitVec.ofNat 64 0x301000 else if i = 1 then 48 else s0.regs i }
theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr_new]; rfl
theorem csW1_rip : csW1.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") := by rw [addr_w1]; rfl
theorem csW2_rip : csW2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") := by rw [addr_w2]; rfl
theorem csMg_rip : csMg.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") := by rw [addr_mg]; rfl
theorem csMv_rip : csMv.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") := by rw [addr_mv]; rfl
theorem csCm_rip : csCm.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") := by rw [addr_cm]; rfl
theorem csIf_rip : csIf.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") := by rw [addr_if]; rfl
theorem csSb_rip : csSb.rip = BitVec.ofNat 64 Fv256.Amd64.UnmarshalTextS.sbAddr := by rw [show Fv256.Amd64.UnmarshalTextS.sbAddr = sbA by decide]; rfl
set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] bW csNew :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_new]; exact Or.inl (⟨rfl, by decide⟩), inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] bW csMg :=
  ⟨⟨by decide, by decide, Or.inl (by decide)⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_mg]; exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, 1, by decide, by decide, by decide⟩)))), inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] bW csMv :=
  ⟨by decide, by rw [addr_mv]; exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, zW, 0x301000, 1, by decide, by decide, by decide⟩))))), inv0, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩, by decide,
    by decide, by decide, by rw [rt_eq]; simp only [calleeStack64, outside_cons, outside_nil]; decide, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide), by simp only [outside_cons, outside_nil]; decide⟩

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] bW csW1 :=
  ⟨by decide, by rw [addr_w1]; exact Or.inr (Or.inl (⟨rfl, by decide⟩)), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] bW csW2 :=
  ⟨by decide, by rw [addr_w2]; exact Or.inr (Or.inr (Or.inl (⟨rfl, by decide⟩))), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre64 16 csCm :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite R0 csIf :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun h => absurd (by decide) h⟩
set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre64 4096 R (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive Fv256.Amd64.UnmarshalTextS.sbAddr [] bW csSb := by
  have hok : R.ok Fv256.Amd64.UnmarshalTextS.sbAddr [(csSb.regs 0).toNat, (csSb.regs 3).toNat, (csSb.regs 1).toNat] := by
    rw [show Fv256.Amd64.UnmarshalTextS.sbAddr = sbA by decide]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, 0, 0x301000, by decide, Or.inl (by decide)⟩)))))
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩, hok, inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩
  · simp [slicebytetostringSpec, argWords64, arg, BufOK, StrIn]; decide
  · simp only [slicebytetostringSpec, argWords64, arg, ReadsOutside, calleeStack64, outside_cons, outside_nil]; decide

/-- The statement of the witness theorem `nonvacuous` (spelled out there). -/
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
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 Fv256.Amd64.UnmarshalTextS.sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive Fv256.Amd64.UnmarshalTextS.sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreU0 cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s :=
  ⟨implA, R, R0, TD, bW, [], loW, hiW, zV, pV, nV, nV, retW, s0,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, by rw [show Fv256.Amd64.UnmarshalTextS.sbAddr = sbA by decide]; exact model_sb,
    ⟨[], bW, csNew, csNew_rip, csNew_pre⟩, ⟨[], bW, csMg, csMg_rip, csMg_pre⟩, ⟨[], bW, csMv, csMv_rip, csMv_pre⟩, ⟨[], bW, csW1, csW1_rip, csW1_pre⟩, ⟨[], bW, csW2, csW2_rip, csW2_pre⟩, ⟨csCm, csCm_rip, csCm_pre⟩, ⟨csIf, csIf_rip, csIf_pre⟩, ⟨[], bW, csSb, csSb_rip, csSb_pre⟩, hret, setup, pre0, hexEnv0⟩

/-- the second call state: the same memory, the input is the hex string at `pH` -/
def s1 : State := { s0 with regs := fun i => if i = 3 then pHV else s0.regs i }

theorem pre1 : PreU0 cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R0 TD bW []
    loW hiW zV pHV nV s1 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26,
    f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37⟩ := pre0
  have e1 : Fv256.Amd64.UnmarshalTextS.sbAddr = sbA := by decide
  rw [e1]
  exact ⟨f1, rfl, f3, f4, f5, f6, f7, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 72, 0x302000, by decide, Or.inr rfl⟩)))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, spW - 40, 0x302000, by decide, Or.inr rfl⟩)))), f10, f11, f12, f13, f14, f15, f16,
    f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, ⟨by decide, by decide⟩, by decide, f37⟩

theorem setup1 : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pHV, nV, nV] s1 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

theorem ishex1 : IsHex s1.mem pHV.toNat nV.toNat := ⟨by decide, by decide, Or.inl (by decide)⟩

theorem hexEnv1 : HexEnv R loW hiW zV s1 := hexEnv0

/-- as `nonvacuous_core`, with the input a `0x…` string (the hex path) -/
theorem hex_core : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
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
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 Fv256.Amd64.UnmarshalTextS.sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive Fv256.Amd64.UnmarshalTextS.sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreU0 cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s ∧ IsHex s.mem pI.toNat nI.toNat :=
  ⟨implA, R, R0, TD, bW, [], loW, hiW, zV, pHV, nV, nV, retW, s1,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, by rw [show Fv256.Amd64.UnmarshalTextS.sbAddr = sbA by decide]; exact model_sb,
    ⟨[], bW, csNew, csNew_rip, csNew_pre⟩, ⟨[], bW, csMg, csMg_rip, csMg_pre⟩, ⟨[], bW, csMv, csMv_rip, csMv_pre⟩, ⟨[], bW, csW1, csW1_rip, csW1_pre⟩, ⟨[], bW, csW2, csW2_rip, csW2_pre⟩, ⟨csCm, csCm_rip, csCm_pre⟩, ⟨csIf, csIf_rip, csIf_pre⟩, ⟨[], bW, csSb, csSb_rip, csSb_pre⟩, hret, setup1, pre1, hexEnv1, ishex1⟩

end Fv256.Amd64.UtWit
