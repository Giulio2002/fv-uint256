import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecInit
import Fv256.Amd64.StrconvMemmove
import Fv256.Amd64.StrconvAppend
import Fv256.Amd64.UdivremM
import Fv256.UtilB2
import Fv256.Util

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- The branch of `Dec`'s loop after the copy: `JNE` at `0x2e3`. -/
abbrev decBr : Nat := Extracted.entry + 0x2e3

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem dec_iter (s0 : State) (b pos y : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hy0 : y ≠ 0) (hy1 : y < 2 ^ 256) (hpos : 19 ≤ pos) (hpos2 : pos ≤ 98)
    (hb : 0x1a0 ≤ b) (hb2 : b + 0x180 ≤ 2 ^ 48)
    (hw : M.accessible (b - 0x1a0) (0x1a0 + 0x180) true = true)
    (hd : Extracted.program.DataLoaded M)
    (hx15 : s0.xmm 15 = 0) (hdf : s0.df = false)
    (e0 : R 0 = BitVec.ofNat 64 pos) (e1 : R 1 = 19#64) (e2 : R 2 = BitVec.ofNat 64 (b + 67))
    (e7 : R 7 = BitVec.ofNat 64 (b + 280)) (e9 : R 9 = BitVec.ofNat 64 (b + 312)) (e4 : R 4 = BitVec.ofNat 64 b)
    (e5 : R 5 = BitVec.ofNat 64 (b + 368))
    (hg3 : M.readLE ((R 14).toNat + 16) 8 + 0x200 < b) (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((R 14).toNat + 16) 8 false = true)
    (hgd : (R 14).toNat + 16 + 8 ≤ b - 0x1a0 ∨ b + 0x180 ≤ (R 14).toNat + 16)
    (hym : Fv256.B.wv M (b + 280) 4 = y) (hdm : Fv256.B.wv M (b + 312) 4 = 10 ^ 19) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decBr)
      { s0 with regs := R, rip := BitVec.ofNat 64 decH, flags := fl, mem := M }
      (fun S' => True) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  have hc2 : decH + 0x5000 < 2 ^ 47 := by decide
  janus64_data hd [hw]
  have hdnz : ¬ (M.readLE (b + 312) 8 + 18446744073709551616 * M.readLE (b + 312 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 312 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 312 + 24) 8 = 0) := by
    intro h
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    omega
  janus64_run [e0, e1, e2, e7, e9, e4, e5, Fv256.Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, hdm, hdnz, Fv256.B.bv128_zero_toNat] until [decBr] calls [Fv256.Amd64.UdivremM.udivrem_rem_s, append_summary, memmove_sum]
  all_goals (try trace_state)
  all_goals sorry
end Fv256.Amd64.Dec
