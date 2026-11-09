import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.PadDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem caseBig (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z n : BitVec 64) (h32 : 32 ≤ n.toNat) (hn : n.toNat ≤ 2 ^ 48)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, n]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, n.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = n.toNat ∧ (s'.regs 2).toNat = n.toNat ∧
        InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) n.toNat = val256 s.mem z.toNat % 2 ^ (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hzd
  janus_run until [Extracted.entry + 0x30] calls [hmk.pos]
  rename_i wobj wregs wflags wvreg wmem wo wx hmf hin hle hacc h8 h16 hzb htr
  have hdj := InRanges.disjoint hin hout
  have hdz := InRanges.disjoint hin hzo
  janus_run [Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.sub_self, BitVec.zero_add, BitVec.add_sub_cancel, Util.bv_add_sub_left]
  have l0 := Util.readLE8_lt s.mem z.toNat
  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
  have hbs : n.toNat ≤ blockSize n.toNat true := by
    unfold blockSize; split
    · exact Nat.le_refl _
    · exact le_roundupsize _ _
  refine ⟨_, rfl, hin.sub (Nat.le_refl _) (by omega), Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), ?_, ?_⟩
  · exact Util.pad_big2 wmem _ n.toNat _ _ _ _ h32 hzb l0 l1 l2 l3
  · janus_frame

end Fv256.Arm64.PaddedBytes
