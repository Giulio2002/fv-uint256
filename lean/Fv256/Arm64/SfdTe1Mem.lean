import Fv256.Arm64.SfdTe1F
import Fv256.Amd64.SfdTeLem

/-!
# `strconv.toError`, write-barrier branch (arm64): memory lemmas for the finished object (extraction-free)

`CH m5 buf t fp q sl e0` is the memory after the stores between the two barriers (slot `buf` of the first barrier, the
fields of the fresh `NumError` `t`); `FM m6 buf1 t e1` the memory after the last two stores (slot of the second barrier,
`t.Err.data`).
-/

open Janus Janus.Arm64 Janus.Spec Janus.Contracts

namespace Fv256.Arm64.SfdToError

def CH (m5 : Janus.Arm64.Memory) (buf t fp q sl e0 : Nat) : Janus.Arm64.Memory :=
  (((((m5.writeLE buf 8 fp).writeLE (buf + 8) 8 q).writeLE t 8 fp).writeLE (t + 16) 8 q).writeLE (t + 24) 8 sl).writeLE
    (t + 32) 8 e0

def FM (m6 : Janus.Arm64.Memory) (buf1 t e1 : Nat) : Janus.Arm64.Memory :=
  (m6.writeLE buf1 8 e1).writeLE (t + 40) 8 e1

set_option maxRecDepth 20000 in
theorem f_fields {m4 m5 m6 : Janus.Arm64.Memory} {Lp : List (Nat × Nat)} {buf buf1 t fl fp q sl e0 e1 : Nat}
    (hLF5 : LiveFrame (m4.writeLE (t + 8) 8 fl) m5 Lp [])
    (hLF6 : LiveFrame (CH m5 buf t fp q sl e0) m6 Lp [])
    (ht : InRanges t 48 Lp) (hA5 : buf + 16 ≤ t ∨ t + 48 ≤ buf) (hA6 : buf1 + 8 ≤ t ∨ t + 48 ≤ buf1)
    (hfl : fl < 2 ^ 64) (hfp : fp < 2 ^ 64) (hq : q < 2 ^ 64) (hsl : sl < 2 ^ 64) (he0 : e0 < 2 ^ 64) (he1 : e1 < 2 ^ 64) :
    (FM m6 buf1 t e1).readLE t 8 = fp ∧ (FM m6 buf1 t e1).readLE (t + 8) 8 = fl ∧
    (FM m6 buf1 t e1).readLE (t + 16) 8 = q ∧ (FM m6 buf1 t e1).readLE (t + 24) 8 = sl ∧
    (FM m6 buf1 t e1).readLE (t + 32) 8 = e0 ∧ (FM m6 buf1 t e1).readLE (t + 40) 8 = e1 := by
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  obtain ⟨r, hr, hr1, hr2⟩ := ht
  have i0 : InRanges t 8 Lp := ⟨r, hr, by omega, by omega⟩
  have i8 : InRanges (t + 8) 8 Lp := ⟨r, hr, by omega, by omega⟩
  have i16 : InRanges (t + 16) 8 Lp := ⟨r, hr, by omega, by omega⟩
  have i24 : InRanges (t + 24) 8 Lp := ⟨r, hr, by omega, by omega⟩
  have i32 : InRanges (t + 32) 8 Lp := ⟨r, hr, by omega, by omega⟩
  unfold FM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hLF6.readLE_nil _ _ i0]; unfold CH
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt hfp
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hLF6.readLE_nil _ _ i8]; unfold CH
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hLF5.readLE_nil _ _ i8]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt hfl
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hLF6.readLE_nil _ _ i16]; unfold CH
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt hq
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hLF6.readLE_nil _ _ i24]; unfold CH
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt hsl
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hLF6.readLE_nil _ _ i32]; unfold CH
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt he0
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt he1

set_option maxRecDepth 20000 in
theorem f_q {m4 m5 m6 : Janus.Arm64.Memory} {Lp : List (Nat × Nat)} {buf buf1 t fl fp q sl e0 e1 bs k : Nat}
    (hLF5 : LiveFrame (m4.writeLE (t + 8) 8 fl) m5 Lp [])
    (hLF6 : LiveFrame (CH m5 buf t fp q sl e0) m6 Lp [])
    (hin : InRanges q bs Lp) (hk : k < bs)
    (hq5 : buf + 16 ≤ q ∨ q + bs ≤ buf) (hq6 : buf1 + 8 ≤ q ∨ q + bs ≤ buf1) (hqt : t + 48 ≤ q ∨ q + bs ≤ t) :
    (FM m6 buf1 t e1).readLE (q + k) 1 = m4.readLE (q + k) 1 := by
  have i1 : InRanges (q + k) 1 Lp := by
    obtain ⟨r, hr, h1, h2⟩ := hin; exact ⟨r, hr, by omega, by omega⟩
  unfold FM
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hLF6.readLE_nil _ _ i1]; unfold CH
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hLF5.readLE_nil _ _ i1]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]

/-- the copied string `q`, read back through the stores into the fresh object and the `newobject` frame -/
theorem m4_copy {m3 m4 M0 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {q bs sl sp k a1 a2 v1 v2 X : Nat}
    (hLF : LiveFrame ((m3.writeLE a1 8 v1).writeLE a2 8 v2) m4 (L ++ [(q, q + bs)]) [])
    (hk : k < sl) (hsl : sl ≤ bs)
    (hd1 : q + k + 1 ≤ a1 ∨ a1 + 8 ≤ q + k) (hd2 : q + k + 1 ≤ a2 ∨ a2 + 8 ≤ q + k)
    (hCop : Mem.Copied M0 m3 q sp sl) (hsrc : M0.readLE (sp + k) 1 = X) :
    m4.readLE (q + k) 1 = X := by
  rw [hLF.readLE_nil _ _ ⟨(q, q + bs), by simp, by omega, by omega⟩]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [Janus.Arm64.Memory.readLE_one, hCop k hk, ← Janus.Arm64.Memory.readLE_one]
  exact hsrc

end Fv256.Arm64.SfdToError
