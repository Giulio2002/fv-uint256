import Fv256.Arm64.SfdTe1F

/-!
# `strconv.toError`, write-barrier branch (arm64): the tail from the entry of `gcWriteBarrier2`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_tail1 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat))
    (fp fl sp sl : BitVec 64) (s S St : State) (m' m2 m3 m4 : Janus.Arm64.Memory) (q t : BitVec 64)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpc : St.pc = BitVec.ofNat 64 (P.contractAddr "runtime.gcWriteBarrier2")) (h0 : St.regs 0 = t)
    (hmem : St.mem = m4.writeLE (t.toNat + 8) 8 fl.toNat) (hlr : St.regs 30 = 618880#64) (hsp : St.sp = s.sp - 96#64)
    (h28 : St.regs 28 = s.regs 28) (h18 : St.regs 18 = s.regs 18)
    (hok1 : R.ok (P.contractAddr "runtime.gcWriteBarrier1") [1]) (hok2 : R.ok (P.contractAddr "runtime.gcWriteBarrier2") [2])
    (F : Pre1 R R2 b L fp fl sp sl s S m' m2 m3 m4 q t) :
    ReachesRet (P.link impl) (s.regs regLR) St (TePost R R2 b L fp fl sp sl s) := by
  obtain ⟨hdep, hlow, e9, e10, hSf, hfr, hMF1, hMF2, hMF3, hLF1, hLF3, hCop, hinvN, hInR, hInT, hApL, hApT, hQsl, hspR, hspP,
    hsdisj, hSm8, oE, pE, qE, hf4, hacc4, hacc4t, hacc4e, hacc4w, hlr4, hfp4, hts4, hte4, hwF, hL18, hrt0, hal, hsp72, e5, pW, qW⟩ := F
  have hsp0 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by rw [BitVec.toNat_sub]; simp; te_omega
  have hSN : St.sp.toNat = s.sp.toNat - 96 := by rw [hsp]; exact hsp0
  have hqw := InRanges.disjoint hInR e9
  have hSacc : s.mem.accessible (s.sp.toNat - 96 - 4096) 4104 true = true := by
    have := Memory.accessible_mono _ e5 (a := s.sp.toNat - 96 - 4096) (n := 4104) (by te_omega) (by te_omega)
    exact this
  janus_run [hmem, h0, hlr, hsp] calls [hw2 := hwb2]
  trace_state
  all_goals sorry

end Fv256.Arm64.SfdToError
