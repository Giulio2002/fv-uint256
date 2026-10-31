import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC
import Fv256.Arm64.MustFromBigSfb

/-!
# `uint256.MustFromBig(b *big.Int) (*Int, bool)` (arm64)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Fv256.Arm64.MustFromBig

/-- the type descriptor and data pointer `MustFromBig` passes to `runtime.gopanic` for `panic("overflow")`, recomputed from the extracted words. -/
def panicType : Nat :=
  adrpLdTarget (Extracted.entry + 0x5c) (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 23)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 24) 0

def panicData : Nat :=
  adrpLdTarget (Extracted.entry + 0x64) (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 25)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 26) 0

def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x30) (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 12)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 13) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (P : PanicRuntime) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168))
      (fun _ => goClass P)
      (fun s s' => (x.toNat = 0 ∨ len.toNat ≤ 4) ∧
        (x.toNat = 0 → s'.regs 0 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])))
      (fun s v _ => x.toNat ≠ 0 ∧ 4 < len.toNat ∧ v = ⟨panicType, panicData⟩) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hfp, hH, hxx⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_eval_nat hpt : panicType
  janus_eval_nat hpd : panicData
  janus_data hd [hw]
  refine GoReturns.of_reaches ?_
  janus_run until [Extracted.entry + 0x3c] calls [hnew.pos]
  · exact ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), fun h => h.elim⟩
  · obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9⟩ := hxx hbr
    simp only [Disjoint] at hx8 hx9
    obtain ⟨hxa, hxb⟩ := hx1
    obtain ⟨hpa, hpb⟩ := hx5
    have hdx := InRanges.disjoint ‹InRanges _ 32 rt› hx6
    have hdp := InRanges.disjoint ‹InRanges _ 32 rt› hx7
    have hds := InRanges.disjoint ‹InRanges _ 32 rt› hout
    janus_run calls [Fv256.Arm64.MustFromBigSfb.sfb_summary impl pw len]
    · rename_i g hxn wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cflag cval cfr
      have hov := Fv256.C.flag_false _ _ cflag hbr
      have h4 := Fv256.C.ovT _ hov
      refine ⟨⟨834016, 1006664⟩, ?_, h4, ?_⟩
      · show (⟨834016, 1006664⟩ : Eface) = ⟨_, _⟩
        simp [setReg]
      · rw [hpt, hpd]
    · rename_i g wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cflag cval cfr
      have hov := Fv256.C.flag_true _ _ cflag hbr
      have hle4 := Fv256.C.ovF_of _ hov
      refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), hle4, fun h => h.elim, _, rfl, hin, h16, hacc, ?_, ?_⟩
      · rw [Fv256.C.bigAbs_write, Fv256.C.bigAbs_frame _ _ _ _ _ hfr, Fv256.C.bigAbs_write, Fv256.C.bigAbs_write,
          Fv256.C.bigAbs_write] at cval
        · exact cval
        all_goals first
          | omega
          | (simp only [outside_append, outside_cons, outside_nil, and_true]
             exact ⟨hx7, by omega, by omega⟩)
      · janus_frame

end Fv256.Arm64.MustFromBig
