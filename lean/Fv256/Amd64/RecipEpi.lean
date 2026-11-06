import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

/-- the post of the whole function: registers, the 40-byte result at `rsp0 + 8`, the frame -/
def RecPost (s s' : State) (mu : Nat) : Prop :=
  s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
  s'.mem.readLE ((s.regs 4).toNat + 8) 40 = mu ∧
  MemFrame s.mem s'.mem [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem epi_d1b {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xd1b)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568) :
    ReachesRet Fv256.RecipProg.program (retAddrOf s) S (fun S' =>
      S'.regs 4 = s.regs 4 + 8#64 ∧ S'.regs 5 = s.regs 5 ∧ S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = s.xmm 15 ∧
      S'.mem = S.mem) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  have hpush := hM.2.1.2.2
  have hret := hM.2.1.2.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  janus64_run [hsp4, hpush]
  all_goals (trace_state; sorry)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem epi_d66 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xd66)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568) :
    ReachesRet Fv256.RecipProg.program (retAddrOf s) S (fun S' =>
      S'.regs 4 = s.regs 4 + 8#64 ∧ S'.regs 5 = s.regs 5 ∧ S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = s.xmm 15 ∧
      S'.mem = S.mem) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  have hpush := hM.2.1.2.2
  have hret := hM.2.1.2.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  janus64_run [hsp4, hpush]
  all_goals (trace_state; sorry)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem epi_d6f {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xd6f)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568) :
    ReachesRet Fv256.RecipProg.program (retAddrOf s) S (fun S' =>
      S'.regs 4 = s.regs 4 + 8#64 ∧ S'.regs 5 = s.regs 5 ∧ S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = s.xmm 15 ∧
      S'.mem = S.mem) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  have hpush := hM.2.1.2.2
  have hret := hM.2.1.2.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  janus64_run [hsp4, hpush]
  all_goals (trace_state; sorry)

end Fv256.Amd64.RecipSeg
