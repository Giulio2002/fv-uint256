import re,sys
root='/srv/fv-uint256-wd/lean/Fv256/'
def gen(op, sname, doc):
    # arm64
    t=open(root+f'Arm64/{op}.lean').read()
    t=t.replace(f'`(*uint256.Int).{op}(x, y) *Int` (arm64): `z = x {"+" if op=="Add" else "-"} y`', f'`(*uint256.Int).I{op}(x *Int) *Int` (arm64): in place, `z = z {"+" if op=="Add" else "-"} x`')
    t=t.replace(f'namespace Fv256.Arm64.{op}',f'namespace Fv256.Arm64.I{op}').replace(f'end Fv256.Arm64.{op}',f'end Fv256.Arm64.I{op}')
    t=t.replace('(z x y : BitVec 64)','(z x : BitVec 64)').replace('[z, x, y]','[z, x]')
    t=t.replace(' ∧ Ptr32 s.mem y false','').replace(' ∧ Aliasing z y ∧ Aliasing x y','')
    t=t.replace(f'(val256 s.mem x.toNat) (val256 s.mem y.toNat)','(val256 s.mem z.toNat) (val256 s.mem x.toNat)')
    t=t.replace('rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy\n  all_goals try subst h\n','rcases hzx with rfl | hzx\n')
    t=t.replace('⟨⟨hz, hz\'⟩, ⟨hx, hx\'⟩, ⟨hy, hy\'⟩, hzx, hzy, hxy⟩','⟨⟨hz, hz\'⟩, ⟨hx, hx\'⟩, hzx⟩')
    t=re.sub(r' \(try have := Util.readLE8_lt s.mem \(y.toNat[^)]*\)\);','',t)
    t=re.sub(r'\(try have := Util.readLE8_lt s.mem \(y.toNat( \+ \d+)?\)\); ','',t)
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
    t=t.replace('correctness z x x ret','correctness z x ret').replace(' else if i = 2 then x\n      else',' \n      else')
    open(root+f'Arm64/I{op}.lean','w').write(t)
gen('Add',0,0); gen('Sub',0,0)
