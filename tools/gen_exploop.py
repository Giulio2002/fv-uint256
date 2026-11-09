import re,sys
src=open('/srv/fv-uint256-wf/lean/Fv256/Proofs/Amd64/ExpLoop1.lean').read()
def gen(v,H,U,keep_ep=True):
    t=src
    t=t.replace('ExpLoop1',f'ExpLoop{v}').replace('head1',f'head{v}').replace('Inv1',f'Inv{v}').replace('loop1',f'loop{v}').replace('0x149',H)
    t=t.replace('k ≤ 64','k ≤ %d'%U).replace('min n 64','min n %d'%U).replace('k < 64','k < %d'%U)
    t=t.replace('S.regs 9 = BitVec.ofNat 64 w ∧ S.regs 8 = BitVec.ofNat 64 ev ∧','S.regs 8 = BitVec.ofNat 64 w ∧')
    t=t.replace('r3, r7, r9, r8, r0, r1,','r3, r7, r8, r0, r1,')
    if not keep_ep:
        t=t.replace(' ∧ S.regs 1 = BitVec.ofNat 64 ep','')
        t=t.replace('r3, r7, r8, r0, r1,','r3, r7, r8, r0,')
    # bullets: rewrite the register bullet block in both branches
    old='''      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.shr1_w64 w hw
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
'''
    n=7 if keep_ep else 6
    new='      · simp [setRegF]\n      · simp [setRegF]\n      · simp [setRegF]; exact Fv256.F.shr1_w64 w hw\n'+'      · simp [setRegF]\n'*(n-3)
    assert t.count(old)==2
    t=t.replace(old,new)
    q='⟨'+', '.join(['?_']*28)+'⟩'
    nq=27 if keep_ep else 26
    assert t.count(q)==2
    t=t.replace(q,'⟨'+', '.join(['?_']*nq)+'⟩')
    return t
for v,H,U,ep in [(2,'0x1f4',128,True),(3,'0x262',192,True),(4,'0x2cc',256,False)]:
    open(f'/srv/fv-uint256-wf/lean/Fv256/Proofs/Amd64/ExpLoop{v}.lean','w').write(gen(v,H,U,ep))
