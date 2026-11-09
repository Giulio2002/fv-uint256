import Janus

/-!
# Contract-inhabitation helpers (extraction-free)

Concrete memories for the U-ICALL-INHABITED lemmas: one writable region `[0, 2^48)` (every in-range window is accessible),
and a memory holding the bytes `bs` at `p`.
-/

open Janus Janus.Arm64 Janus.Contracts Janus.Spec

namespace Fv256.Inhab

/-- one writable region covering the whole canonical address space; all bytes zero -/
def flatMem : Memory := ⟨fun _ => 0, [⟨0, 2 ^ 48, true⟩]⟩

/-- `flatMem` with the bytes `bs` at `p` -/
def strMem (bs : List Nat) (p : Nat) : Memory :=
  ⟨fun a => BitVec.ofNat 8 (bs.getD (a - p) 0), [⟨0, 2 ^ 48, true⟩]⟩

theorem readLE_strMem_far (bs : List Nat) (p a n : Nat) (h : p + bs.length ≤ a) : (strMem bs p).readLE a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Memory.readLE, ih (a + 1) (by omega)]
    have : bs[a - p]? = none := List.getElem?_eq_none (by omega)
    simp [strMem, List.getD_eq_getElem?_getD, this]

theorem accessible_flat (m : Memory) (hm : m.regions = [⟨0, 2 ^ 48, true⟩]) (a n : Nat) (w : Bool)
    (h : a + n ≤ 2 ^ 48) : m.accessible a n w = true := by
  simp [Memory.accessible, hm, h]

theorem accessible_flatMem (a n : Nat) (w : Bool) (h : a + n ≤ 2 ^ 48) : flatMem.accessible a n w = true :=
  accessible_flat flatMem rfl a n w h

theorem accessible_strMem (bs : List Nat) (p a n : Nat) (w : Bool) (h : a + n ≤ 2 ^ 48) :
    (strMem bs p).accessible a n w = true :=
  accessible_flat (strMem bs p) rfl a n w h

theorem strBytes_strMem (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (p : Nat) :
    strBytes (strMem bs p) p bs.length = bs := by
  apply List.ext_getElem
  · simp [strBytes]
  · intro i h1 h2
    simp only [strBytes, List.getElem_map, List.getElem_range, strMem, Nat.add_sub_cancel_left]
    have h3 : bs.getD i 0 = bs[i] := by simp [List.getD_eq_getElem?_getD, h2]
    rw [h3, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hb _ (List.getElem_mem h2); omega)

/-- `StrOut` of the bytes `bs` at `p` in `strMem bs p` -/
theorem strOut_strMem (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (p : Nat) (hp : p + bs.length ≤ 2 ^ 48) :
    StrOut (strMem bs p) p bs.length bs :=
  ⟨rfl, hp, fun _ => accessible_strMem bs p p bs.length false hp, strBytes_strMem bs hb p⟩

/-- `StrOut` survives a store disjoint from the bytes -/
theorem strOut_writeLE {m : Memory} {p n : Nat} {bs : List Nat} (h : StrOut m p n bs) (a k v : Nat)
    (hd : p + n ≤ a ∨ a + k ≤ p) : StrOut (m.writeLE a k v) p n bs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, fun hn => by simpa using h3 hn, by rw [strBytes_writeLE m p n a k v hd]; exact h4⟩


theorem readLE_flatMem (a n : Nat) : flatMem.readLE a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Memory.readLE, ih (a + 1)]
    simp [flatMem]

/-! ### arm64: a call state at `SP = 2^40` -/

/-- an arm64 call state: `X0..X4` as given, the return address `X30 = 0x1000`, `SP = 2^40`, memory `m` -/
def callSt (r0 r1 r2 r3 r4 : W64) (m : Memory) : State :=
  { regs := fun i => if i = 0 then r0 else if i = 1 then r1 else if i = 2 then r2 else if i = 3 then r3
      else if i = 4 then r4 else if i = 30 then 0x1000 else 0,
    sp := BitVec.ofNat 64 (2 ^ 40), pc := 0, flags := default, mem := m }

@[simp] theorem callSt_r0 (a b c d e : W64) (m : Memory) : (callSt a b c d e m).regs 0 = a := by simp [callSt]
@[simp] theorem callSt_r1 (a b c d e : W64) (m : Memory) : (callSt a b c d e m).regs 1 = b := by simp [callSt]
@[simp] theorem callSt_r2 (a b c d e : W64) (m : Memory) : (callSt a b c d e m).regs 2 = c := by simp [callSt]
@[simp] theorem callSt_r3 (a b c d e : W64) (m : Memory) : (callSt a b c d e m).regs 3 = d := by simp [callSt]
@[simp] theorem callSt_r4 (a b c d e : W64) (m : Memory) : (callSt a b c d e m).regs 4 = e := by simp [callSt]
@[simp] theorem callSt_sp (a b c d e : W64) (m : Memory) : (callSt a b c d e m).sp = BitVec.ofNat 64 (2 ^ 40) := rfl
@[simp] theorem callSt_mem (a b c d e : W64) (m : Memory) : (callSt a b c d e m).mem = m := rfl

theorem callSt_pre {r0 r1 r2 r3 r4 : W64} {m : Memory} (hm : m.regions = [⟨0, 2 ^ 48, true⟩]) {nargs stack above : Nat}
    (h8 : 8 ≤ stack) (hs : stack ≤ 2 ^ 40) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ above) {P : State → Prop}
    (hP : P (callSt r0 r1 r2 r3 r4 m)) : Janus.Contracts.ICall.ICallPre nargs stack above [] P (callSt r0 r1 r2 r3 r4 m) := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, h8, ?_, accessible_flat _ hm _ _ _ ?_⟩, hab, trivial, hP⟩ <;>
    simp [callSt, hsp] <;> omega

end Fv256.Inhab

namespace Fv256.Inhab

/-- an amd64 call state: `RAX RBX(3) RDI(7)...` as given (indices 0, 1, 3, 7), `RSP = 2^40`, memory `m` -/
def callSt64 (r0 r1 r3 r6 r7 : BitVec 64) (m : Janus.Arm64.Memory) : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then r0 else if i = 1 then r1 else if i = 3 then r3 else if i = 6 then r6 else if i = 7 then r7
      else if i = 4 then BitVec.ofNat 64 (2 ^ 40) else 0,
    rip := 0, flags := default, xmm := fun _ => 0, mem := m }

@[simp] theorem callSt64_r0 (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).regs 0 = a := by simp [callSt64]
@[simp] theorem callSt64_r1 (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).regs 1 = b := by simp [callSt64]
@[simp] theorem callSt64_r3 (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).regs 3 = c := by simp [callSt64]
@[simp] theorem callSt64_r6 (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).regs 6 = d := by simp [callSt64]
@[simp] theorem callSt64_r7 (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).regs 7 = e := by simp [callSt64]
@[simp] theorem callSt64_r4 (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).regs 4 = BitVec.ofNat 64 (2 ^ 40) := by simp [callSt64]
@[simp] theorem callSt64_mem (a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64 a b c d e m).mem = m := rfl

theorem callSt64_pre {r0 r1 r3 r6 r7 : BitVec 64} {m : Janus.Arm64.Memory} (hm : m.regions = [⟨0, 2 ^ 48, true⟩])
    (hret : m.readLE (2 ^ 40) 8 < 2 ^ 47) {nargs stack above : Nat}
    (hs : stack ≤ 2 ^ 40) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ above) {P : Janus.Amd64.State → Prop}
    (hP : P (callSt64 r0 r1 r3 r6 r7 m)) :
    Janus.Contracts.ICall.ICallPre64 nargs stack above [] P (callSt64 r0 r1 r3 r6 r7 m) := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, accessible_flat _ hm _ _ _ ?_⟩, hab, trivial, hP⟩ <;>
    simp [callSt64, hsp] <;> first | omega | exact hret | skip

end Fv256.Inhab
