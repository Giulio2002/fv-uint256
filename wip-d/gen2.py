import re
root='/srv/fv-uint256-wd/lean/Fv256/'
def rd(isa,op): return open(root+f'{isa}/{op}.lean').read()
def wr(isa,op,t): open(root+f'{isa}/{op}.lean','w').write(t)
def drop_reads(t,v):
    t=re.sub(r' ?\(try have := Util.readLE8_lt s.mem \(%s.toNat( \+ \d+)? ?\)\);'%v,'',t)
    return t
def common(t,isa,op,iop,sym):
    t=t.replace(f'namespace Fv256.{isa}.{op}',f'namespace Fv256.{isa}.{iop}').replace(f'end Fv256.{isa}.{op}',f'end Fv256.{isa}.{iop}')
    return t
def hdr(t,isa,op,iop,sym,uint=False):
    # fix docstring title line and guarantee mentions
    lines=t.split('\n')
    for k,l in enumerate(lines):
        if l.startswith('# `(*uint256.Int).'):
            arg='n uint64' if uint else 'x *Int'
            lines[k]=f'# `(*uint256.Int).{iop}({arg}) *Int` ({isa.lower()}): in place, `z = z {sym} {"n" if uint else "x"}`'
    t='\n'.join(lines)
    t=t.replace('and `y` readable','readable').replace(', `y`',' ')
    return t
# ---------- arm64 ----------
def arm_witness(t,args,regs_fix):
    i=t.index('theorem setup'); j=t.index('theorem returns')
    k=len(args)
    cs=' ∨ '.join(f'i = {n}' for n in range(k))
    pre=t[t.index('theorem hpre'):t.index('theorem nonvacuous')]
    return t[:i],t[j:]
def arm(op,iop,sym,uint):
    t=rd('Arm64',op); t=common(t,'Arm64',op,iop,sym); t=hdr(t,'Arm64',op,iop,sym,uint)
    if not uint:
        t=t.replace('(z x y : BitVec 64)','(z x : BitVec 64)').replace('[z, x, y]','[z, x]')
        t=t.replace(' ∧ Ptr32 s.mem y false','').replace(' ∧ Aliasing z y ∧ Aliasing x y','')
        t=t.replace('(val256 s.mem x.toNat) (val256 s.mem y.toNat)','(val256 s.mem z.toNat) (val256 s.mem x.toNat)')
        t=t.replace('rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy\n  all_goals try subst h\n','rcases hzx with rfl | hzx\n')
        t=t.replace("⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩","⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩")
        t=drop_reads(t,'y')
        i=t.index('theorem setup'); j=t.index('theorem returns')
        t=t[:i]+'''theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

'''+t[j:]
        t=t.replace('correctness z x x ret','correctness z x ret').replace(' else if i = 2 then x\n      else','\n      else')
    else:
        # args z, n ; pre: Ptr32 z true
        t=t.replace('(z x n : BitVec 64)','(z n : BitVec 64)').replace('[z, x, n]','[z, n]')
        t=t.replace(' ∧ Ptr32 s.mem x false ∧ Aliasing z x','')
        t=t.replace('Spec.addU (val256 s.mem x.toNat)','Spec.addU (val256 s.mem z.toNat)').replace('Spec.subU (val256 s.mem x.toNat)','Spec.subU (val256 s.mem z.toNat)')
        t=t.replace("⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩","⟨hz, hz'⟩")
        t=t.replace('  rcases hzx with rfl | hzx\n','')
        t=drop_reads(t,'x')
        i=t.index('theorem setup'); j=t.index('theorem returns')
        t=t[:i]+'''theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true :=
  ⟨by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    Ptr32 s.mem z true :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

'''+t[j:]
        t=t.replace('correctness z x n ret','correctness z n ret')
        t=t.replace('def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)\n','')
        t=t.replace('if i = 0 then z else if i = 1 then x else if i = 2 then n','if i = 0 then z else if i = 1 then n')
    wr('Arm64',iop,t)
# ---------- amd64 ----------
def amd(op,iop,sym,uint):
    t=rd('Amd64',op); t=common(t,'Amd64',op,iop,sym); t=hdr(t,'Amd64',op,iop,sym,uint)
    if not uint:
        t=t.replace('(z x y : BitVec 64)','(z x : BitVec 64)').replace('[z, x, y]','[z, x]')
        t=t.replace(' ∧ Buffer s y 32 false','').replace(' ∧ Alias z y ∧ Alias x y','')
        t=t.replace('(valueAt s x 32) (valueAt s y 32)','(valueAt s z 32) (valueAt s x 32)')
        t=t.replace('rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy\n  all_goals try subst h\n','rcases hzx with rfl | hzx\n')
        t=t.replace("⟨hxw, hx⟩, ⟨hyw, hy⟩, hds, hzx, hzy, hxy⟩","⟨hxw, hx⟩, hds, hzx⟩")
        t=drop_reads(t,'y')
        i=t.index('theorem setup'); j=t.index('theorem returns')
        t=t[:i]+'''theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧
    Disjoint z 32 (s0.regs regSP) 8 ∧ Alias z x :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, Or.inr (by unfold Disjoint; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
      Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

'''+t[j:]
        t=t.replace('correctness z x x ret','correctness z x ret').replace('else if i = 1 then x\n      else','\n      else')
    else:
        t=t.replace('(z x n : BitVec 64)','(z n : BitVec 64)').replace('[z, x, n]','[z, n]')
        t=t.replace(' ∧ Buffer s x 32 false','').replace(' ∧ Alias z x','')
        t=t.replace('(valueAt s x 32) n.toNat','(valueAt s z 32) n.toNat')
        t=t.replace("⟨hxw, hx⟩, hds, hzx⟩","hds⟩").replace('  rcases hzx with rfl | hzx\n','')
        t=drop_reads(t,'x')
        i=t.index('theorem setup'); j=t.index('theorem returns')
        t=t[:i]+'''theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Disjoint z 32 (s0.regs regSP) 8 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Disjoint z 32 (s.regs regSP) 8) :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

'''+t[j:]
        t=t.replace('correctness z x n ret','correctness z n ret').replace('def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)\n','')
        t=t.replace('if i = 3 then x else if i = 1 then n','if i = 3 then n')
    wr('Amd64',iop,t)
import sys
for op,iop,sym,u in [('Add','IAdd','+',0),('Sub','ISub','-',0),('AddUint64','IAddUint64','+',1),('SubUint64','ISubUint64','-',1)]:
    arm(op,iop,sym,u); amd(op,iop,sym,u)
