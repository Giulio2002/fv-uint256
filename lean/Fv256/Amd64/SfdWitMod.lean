import Fv256.Amd64.SfdTopSpec

/-!
# Satisfiability of the amd64 `Mod` and `Env` (Extracted-free), and the regression for the old contradiction

`mod_contra_old` : the OLD `Mod` requirement (every range of `staticRanges C T`, in particular `(T, T + 48)`, outside `R2.priv`)
contradicts `R2.Laws.type_desc` (the descriptor of a model type lies INSIDE `R2.priv`), so the old `TopPre` held of no state.
`modEnv_sat`: the NEW `Mod` and `Env` (with `type_desc` and the `R0` model) are satisfied together by a concrete model (synthetic
`SfdCfg`, hand-laid memory, toy runtime): they are not contradictory.

ISA note: amd64 differs from arm64 here.  arm64's `strconv.toError` needs the `8 ≤ R2.depth` conjunct and the model law `hT`
(the descriptor facts survive any call preserving `R2.Env`); the amd64 `toError` proof needs neither (its ifaceeq call
precondition `CallerOK` holds from the stack window, and the descriptor facts are kept in `StaticOK` and carried by frames that avoid
`staticRanges`), so only the `(T, T+48)` exclusion is needed.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.SfdTopSpec

theorem mod_contra_old (C : SfdCfg) (R2 : IfaceModel) (T : Nat) (m : Janus.Arm64.Memory) (g : BitVec 64)
    (hl : R2.Laws) (hT : R2.IsType T) (hE : R2.Env m g)
    (hold : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) R2.priv) : False := by
  obtain ⟨-, -, -, hin⟩ := hl.type_desc m g T hE hT
  obtain ⟨r, hr, h1, h2⟩ := hin
  have ho : Outside T 48 R2.priv := by
    have := hold (T, T + 48) (by simp [staticRanges])
    simpa using this
  have := MemFrame.outside_mem ho hr
  have h3 : (48 : Nat) = typeDescSize := rfl
  omega

namespace Sat

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.IfaceModel Janus.Contracts.LiveSat

def newA : Nat := 0x7003
def mgA : Nat := 0x7001
def mvA : Nat := 0x7002
def w1A : Nat := 0x7004
def w2A : Nat := 0x7005
def numErrT : Nat := 0xdc840
def pSA : Nat := 0x301000
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [numErrT]) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2]) ∨
  (a = mgA ∧ args = [1, 0, 0]) ∨ (a = mvA ∧ ∃ q, args = [q, pSA, 1])
def R : RtInv := toyR [] ok

def cfgE : SfdCfg := (0x1b5c10, 0x1b5b60, 0x1b6540, 0xdc840, 0xf6940, 0xf6920, 0xf5940, 0x1b5eb0, 0x1e34c0, 0xeb483,
    0xf490b, mgA, mvA, newA, w1A, w2A)

def spW : Nat := 0x100000
def loW : Nat := 0xFEE00
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
  else if a = 0x301000 then 0x37
  else if a = 0xdc840 then 48
  else if a = 0xdc848 then 1
  else if a = 0xf692a then 1
  else if 0xf490b ≤ a ∧ a < 0xf490b + 78 then Fv256.I.maxDigit (a - 0xf490b)
  else if 0x1b6548 ≤ a ∧ a < 0x1b6568 then nb (multW + 32 * ((a - 0x1b6540) / 8 - 1)) 0 ((a - 0x1b6540) % 8)
  else if multW ≤ a ∧ a < multW + 128 then nb (10 ^ (19 * ((a - multW) / 32 + 1))) 0 ((a - multW) % 32)
  else 0

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (val a),
   [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨loW, hiW - loW, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩,
    ⟨0x301000, 1, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0xdc840, 16, false⟩, ⟨0xf490b, 78, false⟩, ⟨0xf5940, 8, false⟩, ⟨0xf6920, 16, false⟩, ⟨0x1b5b60, 16, false⟩,
    ⟨0x1b5c10, 16, false⟩, ⟨0x1b5eb0, 16, false⟩, ⟨0x1b6540, 40, false⟩, ⟨0x1e34c0, 4, false⟩, ⟨multW, 128, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 spW else if i = 14 then BitVec.ofNat 64 gW else 0,
    rip := 0, flags := default, xmm := fun _ => 0, mem := mem0 }

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl



theorem outside_of_decide {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L :=
  Janus.Contracts.outside_of_forall h

theorem mod0 : Mod cfgE R R0 TD [] := by
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

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)

theorem static0 : StaticOK cfgE R0 TD s0.mem := by
  exact ⟨by decide, Or.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env0 : Env cfgE R R0 TD 0x400 [] loW hiW s0 := by
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


theorem modEnv_sat : ∃ (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (s : State),
    Mod cfgE R R2 T L ∧ Env cfgE R R2 T b L lo hi s :=
  ⟨R, R0, TD, 0x400, [], loW, hiW, s0, mod0, env0⟩

end Sat

end Fv256.Amd64.SfdTopSpec

#print axioms Fv256.Amd64.SfdTopSpec.Sat.modEnv_sat
