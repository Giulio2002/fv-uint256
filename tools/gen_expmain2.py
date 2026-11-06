import sys
sys.path.insert(0,'/srv/fv-uint256-wf/tools')
from gen_expmain import block_entry
EP="BitVec.toNat (s.regs 1)"
def E(j): return "(Arm64.Memory.readLE s.mem (%s + %d) 8)"%(EP,8*j) if j else "(Arm64.Memory.readLE s.mem (%s) 8)"%EP
B32="(Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32)"
B8="(Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8)"
def NN(k,c): return f"(63 - Janus.Arm64.clzNat 64 {E(k)} + {c})"
st1=f"(Fv256.F.expIter 64 (1, {B32}, {E(0)}))"
st2=f"(Fv256.F.expIter 64 ({st1}.1, {st1}.2.1, {E(1)}))"
st3=f"(Fv256.F.expIter 64 ({st2}.1, {st2}.2.1, {E(2)}))"
ST={1:st1,2:st2,3:st3}
HEAD={2:('0x1f4','ExpLoop2','loop2','Inv2','head2'),3:('0x262','ExpLoop3','loop3','Inv3','head3'),4:('0x2cc','ExpLoop4','loop4','Inv4','head4')}
def obtain(j,suf):
    if j==1: names="hpc, hk, hr, hb, hw, hev, r3, r7, r8, r9, r0, r1, r2, r6, r4, r5, r14, x15, mr, mb, mz0, mep, mn, mev, hdfS, hmxS, mbp, hfr"
    elif j in (2,3): names="hpc, hk, hr, hb, hw, hev, r3, r7, r8, r0, r1, r2, r6, r4, r5, r14, x15, mr, mb, mz0, mep, mn, mev, hdfS, hmxS, mbp, hfr"
    else: names="hpc, hk, hr, hb, hw, hev, r3, r7, r8, r0, r2, r6, r4, r5, r14, x15, mr, mb, mz0, mep, mn, mev, hdfS, hmxS, mbp, hfr"
    names=", ".join(n+suf if n not in ('mr',) else n+suf for n in names.split(", "))
    return names
def hand(j,k,c,ind):
    """hand-off after loop j (j=1..3) into loop j+1; returns text (bullets at indent ind) of the `intro` bullet; inner continuation placeholder CONT"""
    sp=' '*ind
    s=str(j)
    ob=obtain(j,s)
    nm=ob.split(", ")
    # name lookup helpers
    def N(x): return x+s
    mn_=64*j  # k after loop j = min NN 64j = 64j (since NN > 64j here)
    hd,lmod,lname,inv,head=HEAD[j+1]
    NNs=NN(k,c)
    regs=["r3","r7","r8"]+(["r9"] if j==1 else [])+["r0","r1","r2","r6","r4","r5","r14"]
    if j==4: regs.remove("r1")
    runlist=", ".join(N(x) for x in regs+["mr","mb","mz0","mep","mn","mev"])
    # min rewriting: which hyps contain the min
    minat = " ".join(N(x) for x in ["r3","mr","mb","hr","hb","hw"]+(["r9"] if j==1 else ["r8"]))
    # for j=1 the ghost register fact containing the word is named r8 (regs 9); keep as in verified code
    if j==1: minat=" ".join(N(x) for x in ["r3","mr","mb","hr","hb","hw","r8"])
    # state after: Rj, Bj
    Rj=ST[j]+".1"; Bj=ST[j]+".2.1"
    Ej=E(j)
    t_next=f"(min {NNs} {64*(j+1)} - {64*j})"
    out=f"""{sp}· intro S{s} hI{s}
{sp}  obtain ⟨{ob}⟩ := hI{s}
{sp}  have hmin{s} : min {NNs} {64*j} = {64*j} := by omega_e
{sp}  simp only [hmin{s}] at {minat}
{sp}  have hretS{s} : Arm64.Memory.readLE S{s}.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
{sp}    rw [hfr{s}.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
{sp}  janus64_run [{runlist}] until [Fv256.Amd64.ExpSum.expEntry + {hd}]
{sp}  refine Fv256.Amd64.{lmod}.{lname} s _ {NNs} (BitVec.toNat (s.regs 0)) ({EP}) {B8} hn0 (by omega_e) hnw hacc {t_next} {64*j} {Rj} {Bj} {Ej} _ (by omega_e) ?inv{j+1}_{k} ?hex{j+1}_{k}
{sp}  · unfold Fv256.Amd64.{lmod}.{inv}
"""
    nconj={2:27,3:27,4:26}[j+1]
    out+=f"{sp}    refine ⟨{', '.join(['?_']*nconj)}⟩\n"
    b=[]
    b.append(f"simp [setRegF, Fv256.Amd64.{lmod}.{head}, Fv256.Amd64.ExpSum.expEntry]")
    b.append("omega_e")
    b.append(f"exact hr{s}")
    b.append(f"exact hb{s}")
    b.append("exact Fv256.Util.readLE8_lt _ _")
    b.append(f"exact hev{s}")
    b.append(f"simp [setRegF, {N('r3')}]")
    b.append(f"simp [setRegF, {N('r7')}]")
    b.append("simp [setRegF]")
    b.append(f"simp [setRegF, {N('r0')}]")
    if j+1!=4: b.append(f"simp [setRegF, {N('r1')}]")
    b+= [f"simp [setRegF, {N(x)}]" for x in ["r2","r6","r4","r5","r14"]]
    b.append(f"simp [setRegF, {N('x15')}]")
    b+= [f"exact {N(x)}" for x in ["mr","mb","mz0","mep","mn","mev"]]
    b+= ["rfl","rfl",f"exact {N('mbp')}",f"exact {N('hfr')}"]
    assert len(b)==nconj,(len(b),nconj)
    for x in b: out+=f"{sp}    · {x}\n"
    out+=f"{sp}  · CONT_{j+1}\n"
    return out
if __name__=='__main__':
    print(hand(1,1,65,4))

def final(k,L,c,ind):
    """closing stage after loop L (L=k+1)"""
    sp=' '*ind
    s=str(L)
    ob=obtain(L,s)
    NNs=NN(k,c)
    regs=["r3","r7","r8"]+(["r9"] if L==1 else [])+["r0","r1","r2","r6","r4","r5","r14"]
    if L==4: regs.remove("r1")
    N=lambda x:x+s
    runlist=", ".join(N(x) for x in regs+["mr","mb","mz0","mep","mn","mev"])
    minat=" ".join(N(x) for x in ["r3","mr","mb","hr","hb","hw","r8"])
    EEs={1:f"{E(0)}",2:f"({E(0)} + 2 ^ 64 * {E(1)})",3:f"({E(0)} + 2 ^ 64 * {E(1)} + 2 ^ 128 * {E(2)})",4:f"({E(0)} + 2 ^ 64 * {E(1)} + 2 ^ 128 * {E(2)} + 2 ^ 192 * {E(3)})"}
    EE=EEs[k+1]
    zeros="".join(f", e{j}z" for j in range(k+1,4))
    zeros_rw=f"rw [Fv256.F.split4 s.mem ({EP}){zeros}]" 
    hz={1:"e1nz",2:"e2nz",3:"e3nz"}[k]
    ntop={1:f"Fv256.F.n_top1 {E(0)} {E(1)} (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) {hz}",
          2:f"Fv256.F.n_top2 {E(0)} {E(1)} {E(2)} (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) {hz}",
          3:f"Fv256.F.n_top3 {E(0)} {E(1)} {E(2)} {E(3)} (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) {hz}"}[k]
    rd="(Fv256.Util.readLE8_lt _ _)"
    ex={1:f"Fv256.F.exp_two {B32} {E(0)} {E(1)} {NNs} hBlt {rd} {rd} (by omega_e) (by omega_e) he",
        2:f"Fv256.F.exp_three {B32} {E(0)} {E(1)} {E(2)} {NNs} hBlt {rd} {rd} {rd} (by omega_e) (by omega_e) he",
        3:f"Fv256.F.exp_four {B32} {E(0)} {E(1)} {E(2)} {E(3)} {NNs} 64 rfl hBlt {rd} {rd} {rd} {rd} (by omega_e) (by omega_e) he"}[k]
    # zero-words eE
    if k==3: eEproof="rw [Fv256.F.split4 s.mem (%s)]; omega_e"%EP
    else: eEproof=f"rw [Fv256.F.split4 s.mem ({EP}){zeros}]; omega_e"
    hmin=f"min {NNs} {64*L} = {NNs}"
    out=f"""{sp}· intro S{s} hI{s}
{sp}  obtain ⟨{ob}⟩ := hI{s}
{sp}  have hmin{s} : {hmin} := by omega_e
{sp}  simp only [hmin{s}] at {minat}
{sp}  have hretS{s} : Arm64.Memory.readLE S{s}.mem (BitVec.toNat (s.regs 4)) 8 < 2 ^ 47 := by
{sp}    rw [hfr{s}.readLE _ _ (by simp [Outside] <;> omega_e)]; exact hra2
{sp}  janus64_run [{runlist}]
{sp}  refine ⟨?_, ?_⟩
{sp}  · rw [Fv256.F.copy32 S{s}.mem _ _ _ _ _ (by omega_e) (by omega_e) (by omega_e), {N('mr')}]
{sp}    unfold Fv256.F.expSpec
{sp}    have hBlt : {B32} < Fv256.F.W := by
{sp}      have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
{sp}      simpa using this
{sp}    have hbl : Fv256.Spec.bitLen {EE} = {NNs} := by
{sp}      have := {ntop}
{sp}      exact this
{sp}    have he : {EE} < 2 ^ {NNs} := by
{sp}      have := Fv256.F.bitLen_lt {EE}
{sp}      rw [hbl] at this
{sp}      exact this
{sp}    have hm := {ex}
{sp}    simp only [Fv256.F.MEq] at hm
{sp}    rw [Nat.mod_eq_of_lt {N('hr')}] at hm
{sp}    have eE : Arm64.Memory.readLE s.mem ({EP}) 32 = {EE} := by
{sp}      {eEproof}
{sp}    rw [eE]
{sp}    exact hm
{sp}  · janus_frame
"""
    return out

def top_block(k,c,names):
    out=block_entry(k,names,c,"")
    out+=hand_chain(k,c)
    return out
def indent(txt,n):
    return "".join((' '*n+l if l.strip() else l) for l in txt.splitlines(True))
def hand_chain(k,c):
    # stage 1 at indent 4
    L=k+1
    def build(j,ind):
        if j==L:
            return final(k,L,c,ind)
        t=hand(j,k,c,ind)
        nxt=build(j+1,ind+2)
        return t.replace(" "*(ind+2)+f"· CONT_{j+1}\n",nxt)
    return build(1,4)
if __name__=='__main__':
    pass
