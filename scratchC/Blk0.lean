import Extracted
import Fv256.Amd64.MsaDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)

namespace Fv256.Amd64.Msa

open Fv256.Msa

/-- the element type of the byte slice, an argument of every `growslice` call -/
abbrev ga : Nat := Extracted.program.contractAddr "runtime.growslice"

abbrev u8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem blk0 (impl : List Amd64.Segment) (R : RtInv) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hg : RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive)
    (s S : State) (z : BitVec 64) (dp len0 cap0 b : Nat) (len pp cc : BitVec 64) (L : List (Nat × Nat))
    (Q : Outcome → Prop)
    (hsg : StackGuardOK s 4208) (hal : (s.regs 4).toNat % 8 = 0)
    (hb' : 4208 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hga : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4208) 4232)
    (hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt)
    (hgd : Apart ((s.regs 14).toNat + 16) 8 dp cap0)
    (hzp : s.mem.accessible z.toNat 32 false = true) (hz48 : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : Apart z.toNat 32 ((s.regs 4).toNat - 4208) 4232)
    (hout : Outside ((s.regs 4).toNat - 4208) 4232 R.rt)
    (hdt : Apart u8T 16 ((s.regs 4).toNat - 4208) 4232) (hdtd : Apart u8T 16 dp cap0)
    (hd : Extracted.program.DataLoaded s.mem)
    (hl0 : len.toNat = len0 + 0) (hl0b : len0 < 2 ^ 40) (hs15 : s.xmm 15 = 0)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x20))
    (m : Nat) (hI : BI R ga u8T s S z ret dp len0 cap0 len pp cc b L (m + 1))
    (hcont : ∀ (S' : State) (pp' cc' : BitVec 64) (b' : Nat) (L' : List (Nat × Nat)),
      S'.rip = BitVec.ofNat 64 (Extracted.entry + 0x63) →
      BI R ga u8T s S' z ret dp len0 cap0 (len + 8#64) pp' cc' b' L' m → b - Kc len0 ≤ b' →
      Reaches ((Extracted.program.link impl).withExit ret) S' Q) :
    Reaches ((Extracted.program.link impl).withExit ret) S Q := by
  obtain ⟨hsp, h0, h3, h2, h7, h5, h14, hx15, h_rd1, h_rd2, h_rd3, hw, hfr, hng, hzs, hinv, hLs, hzL, hzpd, hlge, hlle, hlc,
    hC, hPb, hdj, hroom, hgrow, hbud, hrdy, hwho, hpre, hmid⟩ := hI
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw := hsg.noWrap
  have hgrd := hsg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hgb hnw hgrd hb' ha hal hga hgr hgd hw hzd hout hdt hdtd hfr hng h_rd1 h_rd2 h_rd3 hdj hinv hLs hsp h5 h14
  have hlen8 : (len + 8#64).toNat = len.toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hz8 : S.mem.readLE (z.toNat + 0) 8 = s.mem.readLE (z.toNat + 0) 8 := hzs (0) (by omega)
  have hzS : S.mem.accessible z.toNat 32 false = true := by
    rw [hfr.accessible]; exact hzp
  by_cases hl : len.toNat + 8 ≤ cc.toNat
  · obtain ⟨hacc, hdest⟩ := hroom hl
    have hap : Apart (pp.toNat + len.toNat) 8 ((s.regs 4).toNat - 4208) 4232 := by
      unfold Apart at hdj ⊢; omega
    janus64_data hd [hw, hacc, hzS]
    janus64_run until [Extracted.entry + 0x63]
    trace_state
    sorry
  · have hcostK := cost_le len0 len.toNat cc.toNat (by omega) (by omega)
    have hK : Kc len0 ≤ b := by rw [Nat.succ_mul] at hbud; omega
    obtain ⟨hrd⟩ := (⟨hgrow (by omega)⟩ : Nonempty _)
    have hok := (hrdy.1 (by omega)).1
    janus_eval_nat h_ut : u8T
    rw [h_ut] at hdt hdtd hok
    janus64_data hd [hw, hzS]
    janus64_run until [Extracted.entry + 0x47] calls [hg]
    trace_state
    sorry


end Fv256.Amd64.Msa
