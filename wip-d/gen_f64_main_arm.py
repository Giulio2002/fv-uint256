import os
SOLO=os.environ.get('SOLO')
def X(i): return "(s.mem.readLE x.toNat 8)" if i==0 else f"(s.mem.readLE (x.toNat + {8*i}) 8)"
def Y(i): return f"s'.mem.readLE (BitVec.toNat s.sp - {40-8*i}) 8"
def branch(j):
    zs=''.join(f"\n       have hz{i} : {X(i)} = 0 := (show {X(i)} = 0 by janus_assumption)" for i in range(j+1,4))
    zr=''.join(f", hz{i}" for i in range(j+1,4))
    blargs=' '.join(X(i) for i in range(j+1))
    lim=' '.join(f"l{i}" for i in range(j+1))
    c=64*j+64
    leaf=lambda L, extra: f"""refine Fv256.D.{L} _ ({c} - k) _ _ _ _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by omega) (by omega) (by simpa using hbl) m0 m1 m2 m3 (by rw [show 257 - ({c} - k) = {257-c} + k by omega]; exact hS4) (by simp only [Fv256.D.Up, Fv256.D.lsb_ofNat _ 11 (by decide), Fv256.D.lsb0_toNat, Fv256.D.fr_toNat _ m3, Nat.or_eq_zero_iff, beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)"""
    return f'''(
       have hxj : {X(j)} ≠ 0 := (show ¬ {X(j)} = 0 by janus_assumption){zs}
       have hkj : clzNat 64 {X(j)} < 64 := (Fv256.B.clz_cases _ l{j}).resolve_left hxj
       have hbl := Fv256.B.f64_bl{j} {blargs} (clzNat 64 {X(j)}) {lim} hxj rfl
       grab_lsh hS3
       generalize clzNat 64 {X(j)} = k at *
       have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
       have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
       have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
       have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
       have hexp : (18446744073709551616 - (18446744073709551616 - k % 18446744073709551616 + 64 + {64*j}) % 18446744073709551616 + 257) % 18446744073709551616 = {257-c} + k := by omega
       have e8 : BitVec.toNat s.sp - 40 + 8 = BitVec.toNat s.sp - 32 := by omega
       have e16 : BitVec.toNat s.sp - 40 + 16 = BitVec.toNat s.sp - 24 := by omega
       have e24 : BitVec.toNat s.sp - 40 + 24 = BitVec.toNat s.sp - 16 := by omega
       have hS4 := hS3
       simp only [hexp, e8, e16, e24{zr}, Nat.mul_zero, Nat.add_zero] at hS4
       first
        | ({leaf("leaf0","")})
        | ({leaf("leaf1","")}))''' if not SOLO else f'''(have hxj : {X(j)} ≠ 0 := (show ¬ {X(j)} = 0 by janus_assumption){zs}
       have hkj : clzNat 64 {X(j)} < 64 := (Fv256.B.clz_cases _ l{j}).resolve_left hxj
       have hbl := Fv256.B.f64_bl{j} {blargs} (clzNat 64 {X(j)}) {lim} hxj rfl
       grab_lsh hS3
       generalize clzNat 64 {X(j)} = k at *
       have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
       have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
       have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
       have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
       have hexp : (18446744073709551616 - (18446744073709551616 - k % 18446744073709551616 + 64 + {64*j}) % 18446744073709551616 + 257) % 18446744073709551616 = {257-c} + k := by omega
       have e8 : BitVec.toNat s.sp - 40 + 8 = BitVec.toNat s.sp - 32 := by omega
       have e16 : BitVec.toNat s.sp - 40 + 16 = BitVec.toNat s.sp - 24 := by omega
       have e24 : BitVec.toNat s.sp - 40 + 24 = BitVec.toNat s.sp - 16 := by omega
       have hS4 := hS3
       simp only [hexp, e8, e16, e24{zr}, Nat.mul_zero, Nat.add_zero] at hS4
       {leaf(SOLO,"?hn")}'''
bs=[(f'timed "j{j}" ' if os.environ.get('TIMED') else '')+branch(j) for j in [int(c) for c in os.environ.get('BR','321')]]
body='''  janus_run calls [hS := Fv256.Arm64.Float64.lsh_summary (s.sp - 40#64) x]
  all_goals clear_states
  all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat] at *)
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  all_goals have l0 := Util.readLE8_lt s.mem x.toNat
  all_goals have l1 := Util.readLE8_lt s.mem (x.toNat + 8)
  all_goals have l2 := Util.readLE8_lt s.mem (x.toNat + 16)
  all_goals have l3 := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals first
    | ''' + '\n    | '.join(bs) + '''
    | skip
'''
main=open('/srv/fv-uint256-wd/wip-d/f64_arm_main.txt').read()
i=main.index("  janus_run calls")
main=main[:i]+body
main=main.replace("OnlyWrites s.mem s'.mem (s.sp.toNat - 88) 88","MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]")
open('/srv/fv-uint256-wd/wip-d/f64_arm_main2.txt','w').write(main)
