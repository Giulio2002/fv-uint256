import Fv256.Arm64.SfdTePre

/-!
# `strconv.toError` tail, write-barrier flag 0 (arm64): the instructions after the second flag check

From `te + 0xe0` (state `S`, `S.sp = sp0 - 96`, `X0 = t` the fresh `NumError`, `Func.len` already stored): stores `Func`,
`Num`, `Err` into `t`, re-reads the flag (0), returns `numErrItab, t`.  The state at that pc is the hypothesis, so each
try rebuilds only this small file (not the prefix).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

def TailMem (M : Memory) (t : Nat) (fl q sl e0 e1 fn : Nat) : Memory :=
  (((((M.writeLE (t + 8) 8 fl).writeLE t 8 fn).writeLE (t + 16) 8 q).writeLE (t + 24) 8 sl).writeLE (t + 32) 8 e0).writeLE (t + 40) 8 e1

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_tail0 (impl : List Segment) (S : State) (M : Memory) (fl : Nat) (t ret fpv : BitVec 64)
    (hpc : S.pc = BitVec.ofNat 64 (te + 0xe0)) (hmem : S.mem = M.writeLE (t.toNat + 8) 8 fl)
    (h0 : S.regs 0 = t)
    (hlr : M.readLE S.sp.toNat 8 = ret.toNat) (hret4 : ret.toNat % 4 = 0) (hret48 : ret.toNat < 2 ^ 56)
    (hfp : M.readLE (S.sp.toNat - 8) 8 = fpv.toNat)
    (hal : S.sp.toNat % 16 = 0) (hsp : 4096 ≤ S.sp.toNat) (hspt : S.sp.toNat + 168 ≤ 2 ^ 48)
    (hw : M.accessible (S.sp.toNat - 4096) (4096 + 168) true = true)
    (ht48 : t.toNat + 48 ≤ 2 ^ 48) (hacc : M.accessible t.toNat 48 true = true) (hacce : M.accessible strconvErrSyntax 16 false = true)
    (haccf : M.accessible wbFlag 4 false = true) (hflag : M.readLE wbFlag 4 = 0)
    (hts : t.toNat + 48 ≤ S.sp.toNat - 4096 ∨ S.sp.toNat + 168 ≤ t.toNat)
    (hte : strconvErrSyntax + 16 ≤ t.toNat ∨ t.toNat + 48 ≤ strconvErrSyntax)
    (htf : wbFlag + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ wbFlag) :
    ReachesRet (P.link impl) ret S (fun S' =>
      S'.sp = S.sp + 96#64 ∧ S'.regs 0 = BitVec.ofNat 64 numErrItab ∧ S'.regs 1 = t ∧ S'.regs 29 = fpv ∧
      S'.regs 28 = S.regs 28 ∧ S'.regs 18 = S.regs 18 ∧
      S'.mem = TailMem M t.toNat fl (M.readLE (S.sp.toNat + 72) 8) (M.readLE (S.sp.toNat + 56) 8)
        (M.readLE strconvErrSyntax 8) (M.readLE (strconvErrSyntax + 8) 8) (M.readLE (S.sp.toNat + 104) 8)) := by
  have hof : BitVec.ofNat 64 ret.toNat = ret := by simp
  have hof2 : BitVec.ofNat 64 fpv.toNat = fpv := by simp
  have hsp8 : (S.sp + 96#64).toNat = S.sp.toNat + 96 := by rw [BitVec.toNat_add]; simp; omega
  rw [← hlr] at hret4 hret48 hof
  have hlr' : (M.writeLE (t.toNat + 8) 8 fl).readLE S.sp.toNat 8 = ret.toNat := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hlr
  have hacc' : M.accessible t.toNat 48 true = true := hacc
  have hwb : wbFlag = 1979584 := by decide
  have hes : strconvErrSyntax = 1793712 := by decide
  rw [hwb] at htf hflag haccf
  rw [hes] at hte hacce
  rcases htf with htf | htf
  all_goals janus_run [hmem, hlr', hof, hof2, h0, hflag]
  all_goals refine ⟨by rw [hfp]; exact hof2, ?_⟩
  all_goals simp only [TailMem, hes]

end Fv256.Arm64.SfdToError
