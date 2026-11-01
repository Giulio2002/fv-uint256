import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.Amd64.UdivremA
import Fv256.Amd64.KnuthSummary
import Fv256.Amd64.DivWork

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremE

set_option maxHeartbeats 16000000 in
theorem midB (s0 : State) (qp qcap ql ulen n s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn2 : 2 ≤ n) (hulen : ulen ≤ 4) (hulen1 : n ≤ ulen) (hql : ql = 4)
    (hsf : sf + 0x148 ≤ 2 ^ 48) (hsf0 : 0x60 ≤ sf) (hMs : M.accessible (sf - 0x58) 0x1a0 true = true)
    (hqb : qp + 32 ≤ 2 ^ 48) (hqa : M.accessible qp 32 true = true)
    (hqs : qp + 32 ≤ sf - 0x58 ∨ sf + 0x148 ≤ qp)
    (hx15 : s0.xmm 15 = 0) (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M.readLE ((R 14).toNat + 16) 8 < sf - 8) (hgd : (R 14).toNat + 24 ≤ sf - 0x58 ∨ sf + 0x148 ≤ (R 14).toNat + 16)
    (e2 : R 2 = BitVec.ofNat 64 (sf + 72)) (e3 : R 3 = BitVec.ofNat 64 ql) (e10 : R 10 = BitVec.ofNat 64 (ulen + 1)) (e12 : R 12 = BitVec.ofNat 64 n)
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = (if s = 0 then 0#64 else 18446744073709551615#64))
    (e9 : R 9 = BitVec.ofNat 64 qcap) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_f8 : M.readLE (sf + 0xf8) 8 = qp)
    (hdtop : 2 ^ 63 ≤ M.readLE (sf + 0x98 + 8 * (n - 1)) 8)
    (hD : Fv256.B.wv M (sf + 0x48 + 8 * (ulen + 1 - n)) n < Fv256.B.wv M (sf + 0x98) n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x2e5))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x29f), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x2e5), flags := fl', mem := M' } ∧
        R' 4 = BitVec.ofNat 64 sf ∧ R' 5 = R 5 ∧
        Fv256.B.wv M (sf + 0x48) (ulen + 1) = Fv256.B.wv M (sf + 0x98) n * Fv256.B.wv M' qp (ulen + 1 - n) + Fv256.B.wv M' (sf + 0x48) n ∧
        Fv256.B.wv M' (sf + 0x48) n < Fv256.B.wv M (sf + 0x98) n ∧
        M'.readLE (sf + 0xc8) 8 = (18446744073709551616 - s) % 2 ^ 64 ∧ M'.readLE (sf + 0xc0) 8 = (if s = 0 then 0 else 18446744073709551615) ∧
        M'.readLE (sf + 0x90) 8 = ulen + 1 ∧
        MemFrame M M' [(sf + 0x48, sf + 0x48 + 8 * (ulen + 1)), (qp, qp + 8 * (ulen + 1 - n)), (sf - 0x58, sf + 0x38),
          (sf + 0x90, sf + 0x98), (sf + 0xc0, sf + 0xd0)]) := by
  have hcode := ku_lt
  have hql4 : ql < 2 ^ 64 := by omega
  have hn1b : ¬ (BitVec.ofNat 64 n = 1#64) := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [Fv256.B.wv_writeLE_outside, hn1b, e2, e3, e10, e12, e8, e13, e9, e4, m_f8] until [ku + 0x2e5] calls [Fv256.Amd64.KnuthSummary.knuth_summary]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | assumption
    | (have hfr := ‹MemFrame _ _ _›
       rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]
       simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
       first
       | (simp only [Nat.reducePow]; done)
       | (simp only [Nat.reducePow]; split <;> simp_all)
       | (simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega)))
    | (have hfr := ‹MemFrame _ _ _›
       refine Janus.MemFrame.trans (rs := [(sf + 0x90, sf + 0x98), (sf + 0xc0, sf + 0xd0), (sf - 8, sf)]) ?_ hfr ?_
       · janus_frame
       · intro a n' h; simp [Outside] at h ⊢; omega)
  all_goals trace_state

set_option maxHeartbeats 16000000 in
theorem midB1 (s0 : State) (qp qcap ql ulen s sf d0 : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hulen : ulen ≤ 4) (hulen1 : 1 ≤ ulen) (hql : ql = 4)
    (hsf : sf + 0x148 ≤ 2 ^ 48) (hsf0 : 0x60 ≤ sf) (hMs : M.accessible (sf - 0x58) 0x1a0 true = true)
    (hqb : qp + 32 ≤ 2 ^ 48) (hqa : M.accessible qp 32 true = true)
    (hqs : qp + 32 ≤ sf - 0x58 ∨ sf + 0x148 ≤ qp)
    (hx15 : s0.xmm 15 = 0) (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M.readLE ((R 14).toNat + 16) 8 < sf - 8) (hgd : (R 14).toNat + 24 ≤ sf - 0x58 ∨ sf + 0x148 ≤ (R 14).toNat + 16)
    (e2 : R 2 = BitVec.ofNat 64 (sf + 72)) (e3 : R 3 = BitVec.ofNat 64 ql) (e10 : R 10 = BitVec.ofNat 64 (ulen + 1))
    (e9 : R 9 = BitVec.ofNat 64 qcap) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_98 : M.readLE (sf + 0x98) 8 = d0)
    (hd0 : d0 < 2 ^ 64) (hdtop : 2 ^ 63 ≤ d0)
    (hD : M.readLE (sf + 72 + 8 * ulen) 8 < d0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x355))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x32e), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (rr : Nat),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x355), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 rr ∧ R' 4 = BitVec.ofNat 64 sf ∧ R' 14 = R 14 ∧ rr < d0 ∧
        Fv256.B.wv M (sf + 72) (ulen + 1) = d0 * Fv256.B.wv M' qp ulen + rr ∧
        MemFrame M M' [(qp, qp + 8 * ulen), (sf - 16, sf + 8), (sf + 24, sf + 32)]) := by
  have hcode := ku_lt
  janus64_run [Fv256.B.wv_writeLE_outside, e2, e3, e10, e9, e4, m_f8, m_98] until [ku + 0x355] calls [Fv256.Amd64.DivWork2.by1_summary]
  rename_i rr R2 fl2 M2 h0 hk h4 h8 hlt hwv hfr
  refine ⟨R2, fl2, M2, rr, rfl, h0, h4, ?_, hlt, hwv, ?_⟩
  · have := hk 14 (by simp)
    simpa using this
  · refine Janus.MemFrame.trans (rs := [(sf - 8, sf)]) ?_ hfr ?_
    · janus_frame
    · intro a n' h; simp [Outside] at h ⊢; omega

end Fv256.Amd64.UdivremE
