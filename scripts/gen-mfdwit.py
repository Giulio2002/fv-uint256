#!/usr/bin/env python3
# generate arm64 MustFromDecimal witness files MFdWitA/B/C from FdWitA/B/C (+ PanicInit part)
import re
D='/srv/fv-uint256-wJ/lean/Fv256/Arm64/'
for x in 'ABC':
    s=open(D+'FdWit%s.lean'%x).read()
    s=s.replace('FdWit','MFdWit')
    s=re.sub(r'Fv256\.Arm64\.FromDecimal(?!Spec)','Fv256.Arm64.MustFromDecimal',s)
    if x=='C':
        i=s.index('theorem pre0')
        j=s.index('theorem hret')
        new='''theorem ioeof0 : s0.mem.readLE cfg.ioEOF 8 = 0xf6940 := by rw [cfg_lit]; decide
theorem errbig0 : s0.mem.readLE cfg.errBig 8 = 0xf6940 := by rw [cfg_lit]; decide

theorem panicInit0 : PanicInit cfg R (R3 TW) loW hiW s0.mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w = 0xf6940 := by
      rcases hw with h | h
      · rw [h]; exact ioeof0
      · rw [h]; exact errbig0
    subst hw'
    refine ⟨by decide, by decide, ?_, ?_⟩
    · rw [rt_eq]; apply outside_of_decide; decide
    · apply outside_of_decide; decide
  · rw [cfg_lit, rt_eq]; apply outside_of_decide; decide
  · rw [cfg_lit]; apply outside_of_decide; decide
  · rw [cfg_lit]; simp only [R3_priv]; apply outside_of_decide; decide
  · rw [cfg_lit]; decide

'''
        pre=s[i:j]
        pre=pre.replace("have hi := initDone0\n","have hi := initDone0\n  have hp := panicInit0\n").replace("⟩, dataLoaded0⟩","⟩, dataLoaded0, hp⟩")
        s=s[:i]+new+pre+s[j:]
        s=s.replace("(pS nS : BitVec 64) (ret : Nat) (s : State),\n    ImplApart","(pS nS : BitVec 64) (P : Janus.Spec.PanicRuntime) (ret : Nat) (s : State),\n    ImplApart")
        s=s.replace("    Fv256.Arm64.MustFromDecimal.Pre R R2 T b L lo hi pS nS s :=\n  ⟨implA, R, R3 TW, TW, 0x400, [], loW, hiW, pSV, nSV, retW,","    (pinPanicRuntime P ∧ Fv256.Arm64.MustFromDecimal.Pre R R2 T b L lo hi pS nS s) :=\n  ⟨implA, R, R3 TW, TW, 0x400, [], loW, hiW, pSV, nSV, Janus.Contracts.PanicModel.P0 [] 0, retW,")
        s=s.replace("hret, setup, pre0⟩","hret, setup, ⟨trivial, pre0⟩⟩")
        s=s.replace("/-- The statement of the witness","/-- pins the type of an existential variable of `nonvacuous` -/\ndef pinPanicRuntime (_k : Janus.Spec.PanicRuntime) : Prop := True\n\n/-- The statement of the witness")
    open(D+'MFdWit%s.lean'%x,'w').write(s)
