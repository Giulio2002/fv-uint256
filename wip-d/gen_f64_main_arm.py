def X(i): return "s.mem.readLE x.toNat 8" if i==0 else f"s.mem.readLE (x.toNat + {8*i}) 8"
def Y(i): return f"s'.mem.readLE (BitVec.toNat s.sp - {40-8*i}) 8"
def branch(j):
    zs=''.join(f"\n       have hz{i} : {X(i)} = 0 := ‹{X(i)} = 0›" for i in range(j+1,4))
    blargs=' '.join(X(i) for i in range(j+1))
    lim=' '.join(f"l{i}" for i in range(j+1))
    Vexpr=' + '.join(['%s' % X(0)]+[f"{[0,18446744073709551616,340282366920938463463374607431768211456,6277101735386680763835789423207666416102355444464034512896][i]} * {X(i)}" for i in range(1,j+1)])
    c=64*j+64
    return f'''(have hxj : {X(j)} ≠ 0 := ‹¬ {X(j)} = 0›{zs}
       have hkj : clzNat 64 {X(j)} < 64 := (Fv256.B.clz_cases _ l{j}).resolve_left hxj
       have hbl := Fv256.B.f64_bl{j} {blargs} (clzNat 64 {X(j)}) {lim} hxj rfl
       have hS3 := ‹val256 s'.mem _ = Spec.lsh _ _›
       generalize clzNat 64 {X(j)} = k at *
       have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
       have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
       have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
       have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
       have hsp40 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by rw [BitVec.toNat_sub]; simp; omega
       have hsh : (257#64 - (64#64 - BitVec.ofNat 64 k + {64*j}#64)).toNat = {257-c} + k := by
         rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]; simp; omega
       simp (disch := omega) only [val256, Spec.lsh, Spec.W, setReg_apply, hsp40, hsh, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hS3
       simp only [lsb_ofNat _ 11 (by decide), lsb0_toNat, fr_toNat _ m3, Nat.or_eq_zero_iff] at *
       sorry)'''
bs=[branch(j) for j in (3,2,1)]
body='''  janus_run calls [hS := Fv256.Arm64.Float64.lsh_summary (s.sp - 40#64) x]
  all_goals clear_states
  all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat] at *)
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  have l0 := Util.readLE8_lt s.mem x.toNat
  have l1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals first
    | ''' + '\n    | '.join(bs) + '''
    | sorry
'''
main=open('/srv/fv-uint256-wd/wip-d/f64_arm_main.txt').read()
i=main.index("  janus_run calls")
main=main[:i]+body
main=main.replace("OnlyWrites s.mem s'.mem (s.sp.toNat - 88) 88","MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]")
open('/srv/fv-uint256-wd/wip-d/f64_arm_main2.txt','w').write(main)
