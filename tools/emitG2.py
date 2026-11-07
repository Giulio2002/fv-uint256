import sys,subprocess
sys.path.insert(0,'.')
from genG1 import *
HEAD='''  skip
'''
def concrete(v):
    # sz1 -> readLE s.mem (z.toNat + 8) 8
    if v=='0': return '0'
    off={'0':'','1':' + 8','2':' + 16','3':' + 24'}[v[2]]
    return f"(Janus.Arm64.Memory.readLE s.mem ({v[1]}.toNat{off}) 8)"
def bound(v):
    if v=='0': return '(by omega_s)'
    off={'0':'','1':' + 8','2':' + 16','3':' + 24'}[v[2]]
    return f"(Fv256.Util.readLE8_lt s.mem ({v[1]}.toNat{off}))"
def closer(i):
    hy,g=split(cs[i])
    gg=abst(san(g))
    body=re.search(r'F\.addmodSpec (.*)$',gg).group(1)
    X,Y,M=[limbs(a) for a in args_of(body)]
    xs=' '.join(concrete(v) for v in X+Y)
    bs=' '.join(bound(v) for v in X+Y)
    bh=''.join(f'  have bnd{k} := {bound(v)}\n' for k,v in enumerate(X+Y) if v!='0')
    return f'''  have key := KEYNAME
  clear CLEARS
  simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
  have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
  have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
  have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
  have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
  have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
  have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
  have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
  have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
  simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
{bh}  have hv := Fv256.F.add4_val {xs} {bs}
  have hf := Fv256.F.add4_flag {xs} {bs}
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
  have ho := Fv256.F.ov_of _ (by assumption)
  rw [key]
  unfold Fv256.F.addmodSpec
  rw [if_neg (by omega_s)]
  refine congrArg (fun t => t % _) ?_
  all_goals (decide_facts; omega_s)
'''
if __name__=='__main__':
    i=int(sys.argv[1])
    subprocess.run(['python3','mkex.py','genx.out',str(i),f'g2_{i}.lean'],capture_output=True)
    t=open(f'g2_{i}.lean').read()
    t=t.split('\n../scratch/')[0].rstrip()
    if not t.endswith('sorry'): t+=' := by\n  sorry\n'
    extra=" (hrodv : s.mem.readLE 5184344 16 = 18446744073709551616) (hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat) (hxd : x.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ x.toNat) (hyd : y.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ y.toNat) (hmd : m.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ m.toNat)"
    k=t.rindex(" :\n  ")
    t=t[:k]+extra+t[k:]
    j=t.rindex('  sorry')
    t=t[:j]+closer(i).replace('KEYNAME','left_d').replace('CLEARS','left_d1 left_d right_d')
    open(f'g2_{i}.lean','w').write(t)
