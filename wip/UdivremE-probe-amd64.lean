import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.Amd64.UdivremA
import Fv256.Amd64.KnuthSummary

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremE

set_option maxHeartbeats 16000000 in
theorem mid3_probe (s0 : State) (qp qcap ql up ulen n s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn2 : 2 ≤ n) (hulen : ulen ≤ 4) (hulen1 : n ≤ ulen) (hql : ql = 4)
    (hup : up + 32 ≤ 2 ^ 48) (hua : M.accessible up 32 false = true)
    (hsf : sf + 0x148 ≤ 2 ^ 48) (hsf0 : 0x60 ≤ sf) (hMs : M.accessible (sf - 0x58) 0x1a0 true = true)
    (hqb : qp + 32 ≤ 2 ^ 48) (hqa : M.accessible qp 32 true = true)
    (hdisj : up + 32 ≤ sf - 0x58 ∨ sf + 0x148 ≤ up) (hqs : qp + 32 ≤ sf - 0x58 ∨ sf + 0x148 ≤ qp)
    (hx15 : s0.xmm 15 = 0) (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M.readLE ((R 14).toNat + 16) 8 < sf - 8) (hgd : (R 14).toNat + 24 ≤ sf - 0x58 ∨ sf + 0x148 ≤ (R 14).toNat + 16)
    (e0 : R 0 = 0#64) (e1 : R 1 = 0 - BitVec.ofNat 64 s) (e2 : R 2 = BitVec.ofNat 64 (sf + 72)) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 (ulen + 1)) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = (if s = 0 then 0#64 else 18446744073709551615#64)) (e15 : R 15 = 18446744073709551615#64)
    (e9 : R 9 = BitVec.ofNat 64 qcap) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_100 : M.readLE (sf + 0x100) 8 = ql)
    (hdtop : 2 ^ 63 ≤ M.readLE (sf + 0x98 + 8 * (n - 1)) 8)
    (hD : Fv256.B.wv M (sf + 0x48 + 8 * (ulen + 1 - n)) n < Fv256.B.wv M (sf + 0x98) n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x2e5))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M } (fun S' => False) := by
  have hcode := ku_lt
  have hql4 : ql < 2 ^ 64 := by omega
  janus64_run [Fv256.B.wv_writeLE_outside, e0, e1, e2, e3, e7, e10, e11, e8, e13, e15, e9, e4, m_b8, m_f8, m_100] until [ku + 0x2e5] calls [Fv256.Amd64.KnuthSummary.knuth_summary]
  all_goals trace_state

end Fv256.Amd64.UdivremE
