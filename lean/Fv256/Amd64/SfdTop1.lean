import Fv256.Amd64.SfdTopBr

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

abbrev sfd : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
theorem probe1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 sfd)
    (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s (TopPost extCfg R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv' := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hgl : Amd64.load s.mem ((s.regs 14).toNat + 16) 8 = .ok (s.mem.readLE ((s.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  have hacc : s.mem.accessible ((s.regs 4).toNat - 64) 88 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  janus64_run [h0, h1, h3, hacc] until [sfd + 0xe0, sfd + 0x57]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.SfdTop
