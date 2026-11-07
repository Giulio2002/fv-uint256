import Extracted
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanWitB

/-!
# Witness for `SetFromDecimal` (amd64), part C: a concrete call state

`SetFromDecimal(z, "7")` with the toy runtime `R`, the interface model `R0`, a stack window `[lo, hi)`, and a memory laid out
by hand (`mem0`): the model's metadata, the heap, the binary's static objects the proof reads (at the extraction's own
addresses, with synthetic contents), the four multiplier objects `10^(19 k)`, `z`, the string.
-/

open Fv256.Amd64.ScanCfg
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.Scan.Wit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.IfaceModel

def spW : Nat := 0x100000
def loW : Nat := 0xFD000
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def zW : Nat := 0x300000
def multW : Nat := 0x501000

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the synthetic contents of `mem0` -/
def val (a : Nat) : Nat :=
  if 0x10000 ≤ a ∧ a < 0x11000 then (IfaceModel.wmem.bytes a).toNat
  else if a = 0x400003 then 0x10
  else if a = 0x100001 then 0x10
  else if a = 0x301000 then 0x37
  else if 0x302000 ≤ a ∧ a < 0x302008 then nb 0x301000 0x302000 a
  else if a = 0x302008 then 1
  else if a = 0x4d78a0 then 48
  else if a = 0x4d78a8 then 1
  else if a = 0x4f19ea then 1
  else if 0x4ef9b4 ≤ a ∧ a < 0x4ef9b4 + 78 then Fv256.I.maxDigit (a - 0x4ef9b4)
  else if 0x5b8588 ≤ a ∧ a < 0x5b85a8 then nb (multW + 32 * ((a - 0x5b8580) / 8 - 1)) 0 ((a - 0x5b8580) % 8)
  else if multW ≤ a ∧ a < multW + 128 then nb (10 ^ (19 * ((a - multW) / 32 + 1))) 0 ((a - multW) % 32)
  else 0

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (val a),
   [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨loW, hiW - loW, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩,
    ⟨0x301000, 0x1000, false⟩, ⟨0x302000, 16, false⟩, ⟨0x5df444, 1, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0x4d78a0, 16, false⟩, ⟨0x4ef9b4, 78, false⟩, ⟨0x4f09f0, 8, false⟩, ⟨0x4f19e0, 16, false⟩, ⟨0x5b7ba0, 16, false⟩,
    ⟨0x5b7c50, 16, false⟩, ⟨0x5b7ef0, 16, false⟩, ⟨0x5b8580, 40, false⟩, ⟨0x5def20, 4, false⟩, ⟨multW, 128, false⟩]⟩

def zV : BitVec 64 := BitVec.ofNat 64 zW
def pSV : BitVec 64 := BitVec.ofNat 64 0x301000
def retW : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then pSV else if i = 1 then 1#64
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
  simp only [val, multW]
  repeat rw [if_neg (by omega)]
  exact if_neg (by omega)

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (val i) = 0
  rw [val_big i (by simp only [HEAP] at h; omega)]; rfl

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)

theorem static0 : StaticOK cfg R0 TD s0.mem := by
  rw [cfg_lit]
  exact ⟨by decide, Or.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env0 : Env cfg R R0 TD 0x400 [] loW hiW s0 := by
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
    simp only [val, multW]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    rw [Nat.add_sub_cancel_left]
  have h2 : Fv256.I.maxDigit k < 256 := by
    unfold Fv256.I.maxDigit
    have := Nat.mod_lt ((2 ^ 256 - 1) / 10 ^ (77 - k)) (by decide : 0 < 10)
    omega
  rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h2

theorem chunk0 : ChunkAll cfg R R0 [] 0x400 pSV.toNat (1#64).toNat loW hiW s0.mem := by
  rw [cfg_lit]
  intro sp sl h1 h2 h3 h4
  have e1 : pSV.toNat = 0x301000 := by decide
  have e2 : (1#64).toNat = 1 := by decide
  rw [e1] at h1 h2; rw [e2] at h2
  have hsp : sp = 0x301000 := by omega
  have hsl : sl = 1 := by omega
  subst hsp hsl
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), fun q => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, q, rfl⟩))),
    by decide, by decide, by decide, by decide, ?_, ?_⟩
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide

theorem pre0 : TopPre cfg R R0 TD 0x400 [] loW hiW zV pSV 1#64 s0 := by
  have e : cfg = _ := cfg_lit
  have hm := maxdig0
  have hc := chunk0
  rw [e] at hm hc ⊢
  refine ⟨⟨by decide, by decide, by decide, by decide⟩, rfl, rfl, rfl, mod0, env0, by decide, by decide, mult0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · apply outside_of_decide; decide
  · decide
  · apply outside_of_decide; decide
  · decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · exact hm
  · exact ⟨by decide, by decide⟩
  · decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide
  · exact ⟨by decide, Or.inr (by decide)⟩
  · decide
  · decide
  · exact hc

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by rw [linked_eq]; decide)

theorem setup : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pSV, 1#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl, rfl⟩

end Fv256.Amd64.Scan.Wit
