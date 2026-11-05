import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.UtilI

/-!
# `runtime.decoderune(s, k)` (amd64), as a callee of `SetFromDecimal`

`SetFromDecimal` strips leading zeros with `for i, c := range s { if c != '0' { break } }`; for a byte `>= 0x80`
the compiled `range` calls `runtime.decoderune`.  All that the caller needs: the decoded rune is never `'0'`
(it is `>= 0x80`: a decoded multi-byte rune is `> 0x7f` and the error rune is `U+FFFD`).  Proved by running the code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SfdDecode

abbrev dr : Nat := segAddr Extracted.program "runtime.decoderune"

def DecPre (p k len : BitVec 64) (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.xmm 15 = 0 ∧ s.df = false) ∧
  s.regs 0 = p ∧ s.regs 3 = len ∧ s.regs 1 = k ∧ Buffer s p len.toNat false ∧ k.toNat < len.toNat ∧
  StackWritable s 8 16 ∧
  (p.toNat + len.toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 16 ≤ p.toNat)

def DecPost (s s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
  128 ≤ (s'.regs 0).toNat ∧ (s'.regs 0).toNat < 2 ^ 32 ∧
  MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem decoderune_sum (impl : List Janus.Amd64.Segment) (p k len : BitVec 64) :
    Summary (Extracted.program.link impl) dr (DecPre p k len) DecPost := by
  intro s hpc ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, ⟨hpw, hp⟩, hk, ⟨hlow, hnw, hacc⟩, hdisj⟩
  simp only [regSP] at hacc hlow hnw
  have hlen : len.toNat < 2 ^ 63 := by omega
  have hd : (len - k).toNat = len.toNat - k.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hm : ((0#64 - (len - k)).sshiftRight 63).toNat &&& k.toNat = k.toNat :=
    Fv256.I.mask_keep (len - k) k (by omega) (by omega)
  have hk1 := Janus.Arm64.Memory.readLE_lt s.mem (p.toNat + k.toNat) 1
  janus64_run [hm]
  all_goals (unfold DecPost)
  all_goals (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals first | janus_frame | (simp [retAddrOf, setRegF_apply, hdf]; done) | skip
  all_goals (try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff])
  all_goals (try (simp [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; done))
  all_goals (try exact Fv256.I.g2 _)
  all_goals (try (simp; done))
  all_goals (try exact Fv256.I.g1 _ (Fv256.I.jle32_not_127 _ (by first | with_reducible assumption | janus_assumption)))
  all_goals (try exact Fv256.I.g1 _ (Nat.le_trans (by omega) (Fv256.I.jle32_not_2047 _ (by first | with_reducible assumption | janus_assumption))))
  rename_i b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0
  simp only [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_shiftLeft, Nat.reducePow, Nat.reduceMod] at b0 ⊢
  omega

end Fv256.Amd64.SfdDecode
