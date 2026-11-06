import Extracted
import Fv256.Amd64.SfdFd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd
abbrev head : Nat := fd + 0xa0

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
example (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) :
    Summary (Extracted.program.link impl) fd (FdPre R R2 T b L lo hi z pS nS) (FdPost R R2 T b L lo hi z pS nS) := by
  intro s hpc ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hgl : Amd64.load s.mem ((s.regs 14).toNat + 16) 8 = .ok (s.mem.readLE ((s.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  have hio : ioEOF = 5995600 := by decide
  have hmt : mulTab = 5997952 := by decide
  obtain ⟨hM1, hM2, hM3⟩ := hMult
  have hEOFo' := hEOFo
  have hM2' := hM2
  rw [hio] at hEOFo'
  rw [hmt] at hM2'
  simp only [outside_cons, outside_nil, and_true] at hEOFo' hM2'
  by_cases hn0 : nS = 0
  · janus64_run
    trace_state
    sorry
  · janus64_run until [head]
    trace_state
    sorry
