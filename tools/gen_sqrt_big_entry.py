#!/usr/bin/env python3
"""bullets for the three cases (limb j = 1,2,3 holds the top bit) of arm64 sqrt_big"""
import sys
def XR(i): return "s.mem.readLE (s.regs 1).toNat 8" if i==0 else f"s.mem.readLE ((s.regs 1).toNat + {8*i}) 8"
C=["","18446744073709551616","340282366920938463463374607431768211456","6277101735386680763835789423207666416102355444464034512896"]
def bullet(j, ind):
    off=64*j+1; BL=f"{64*j+64} - k"; N=f"(64 - k + {off}) / 2"
    zs=[i for i in range(j+1,4)]
    zl="".join(f", h{i}z" for i in reversed(zs))
    L=[]
    L.append(f"-- limb {j}")
    L.append(f"have hx{j} : {XR(j)} ≠ 0 := by omega")
    L.append(f"obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 ({XR(j)}) = k := ⟨_, rfl⟩")
    L.append(f"have hkj : k < 64 := by")
    L.append(f"  have := Util.clz_bl 64 ({XR(j)}) hl{j}; have := SqrtHead.bl_pos _ hx{j}; omega")
    L.append(f"have hcv := cnt_val k {off} (by omega) (by omega)")
    L.append(f"have hc33 : 33 ≤ {N} := by omega")
    L.append(f"have hc128 : {N} ≤ 128 := by omega")
    if j==2:
        L.append(f"have hxo : ({XR(2)}) ||| ({XR(1)}) ≠ 0 := by")
        L.append(f"  intro h; rw [Nat.or_eq_zero_iff] at h; omega")
    if j==3:
        L.append(f"have hxo : ({XR(2)}) ||| ({XR(1)}) ||| ({XR(3)}) ≠ 0 := by")
        L.append(f"  intro h; simp only [Nat.or_eq_zero_iff] at h; omega")
    L.append(f"janus_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hk, hcv, hc33, hc128, hx{j}{', hxo' if j>=2 else ''}{zl}] until [headB, headS]")
    L.append(f"  calls [lsh_summary, rsh_summary]")
    L.append("trace_state") if False else None
    L.append("rename_i s1 pc1 pc1' sp1 r18a r28a r29a r30a r0a hLv hLf pc2 pc2' sp2 r18b r28b r29b r30b r0b hRv hRf")
    # X forms
    sumj=" + ".join([XR(0)]+[f"{C[i]} * {XR(i)}" for i in range(1,j+1)])
    L.append(f"have hXj : s.mem.readLE (s.regs 1).toNat 32 = {sumj} := by")
    L.append(f"  rw [Util.readLE_32] <;> omega")
    full=" + ".join([XR(0)]+[f"{C[i]} * {XR(i) if i<=j else '0'}" for i in range(1,4)])
    L.append(f"have hXb : s.mem.readLE (s.regs 1).toNat 32 = {full} := by")
    L.append(f"  rw [Util.readLE_32] <;> omega")
    args=" ".join("("+XR(i)+")" for i in range(j+1))
    lims=" ".join(f"hl{i}" for i in range(j+1))
    L.append(f"have hbl : Spec.bitLen (s.mem.readLE (s.regs 1).toNat 32) = {BL} := by")
    L.append(f"  rw [hXb]; exact Fv256.B.f64_bl{j} {args} k {lims} hx{j} hk")
    L.append(f"obtain ⟨hc1, hc128', hXinv, hX64, hX256⟩ := SqrtHead.head_arith _ ({BL}) ({N}) hbl (by omega) (by omega) (by omega)")
    L.append(f"have hlsh : Spec.lsh 1 ({N}) = 2 ^ ({N}) := by")
    L.append(f"  unfold Spec.lsh Spec.W")
    L.append(f"  rw [Nat.one_mul]")
    L.append(f"  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))")
    L.append(f"rw [hlsh] at hLv")
    L.append(f"have hsumA : s'.mem.readLE (s.sp.toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE (s.sp.toNat - 40 + 8) 8 +")
    L.append(f"    2 ^ 128 * s'.mem.readLE (s.sp.toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE (s.sp.toNat - 40 + 24) 8 = 2 ^ ({N}) := by")
    L.append(f"  rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),")
    L.append(f"    hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]")
    L.append(f"  exact hLv")
    L.append("have f1 : s.sp.toNat - 72 + 8 = s.sp.toNat - 64 := by omega")
    L.append("have f2 : s.sp.toNat - 72 + 16 = s.sp.toNat - 56 := by omega")
    L.append("have f3 : s.sp.toNat - 72 + 24 = s.sp.toNat - 48 := by omega")
    L.append("have g1 : s.sp.toNat - 40 + 8 = s.sp.toNat - 32 := by omega")
    L.append("have g2 : s.sp.toNat - 40 + 16 = s.sp.toNat - 24 := by omega")
    L.append("have g3 : s.sp.toNat - 40 + 24 = s.sp.toNat - 16 := by omega")
    L.append("simp only [f1, f2, f3, ← hXj, Spec.rsh] at hRv")
    L.append("simp only [g1, g2, g3] at hsumA")
    L.append("simp (config := { decide := true, failIfUnchanged := false }) only [setReg_apply, ↓reduceIte] at r18a r28a r29a r18b r28b r29b")
    L.append("have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by")
    L.append("  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega")
    L.append("have hs0 := (s.regs 0).isLt")
    L.append("have hs1 := (s.regs 1).isLt")
    L.append("have hs29 := (s.regs 29).isLt")
    L.append("have hs30 := (s.regs 30).isLt")
    rd="simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]"
    mem=lambda: f"show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; {rd} <;> omega"
    L.append("refine big_loop s _ h30a h30b hal hsp hspb hwin hg1 hg2 hg3 hdg hzb hza hdz hxb hxa hdx hX64 hX256 rfl (2 ^ ("+N+"))")
    L.append("  (s'.mem.readLE (s.sp.toNat - 40) 8) (s'.mem.readLE (s.sp.toNat - 32) 8) (s'.mem.readLE (s.sp.toNat - 24) 8) (s'.mem.readLE (s.sp.toNat - 16) 8)")
    L.append("  (s'.mem.readLE (s.sp.toNat - 72) 8) (s'.mem.readLE (s.sp.toNat - 64) 8) (s'.mem.readLE (s.sp.toNat - 56) 8) (s'.mem.readLE (s.sp.toNat - 48) 8)")
    L.append("  _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) hXinv")
    L.append("case inv =>")
    L.append("  refine ⟨?pc, ?sp, ?r18, ?r28, ?r29, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?mfp, ?mz, ?mx,")
    L.append("    Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,")
    L.append("    Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?fr⟩")
    L.append("  case pc => simp only [headB, reduceSegAddr, Nat.reduceAdd]")
    L.append("  case sp => exact e144")
    L.append("  case r18 => exact r18b.trans r18a")
    L.append("  case r28 => exact r28b.trans r28a")
    L.append("  case r29 => exact r29b.trans r29a")
    for nm in ["mret","mfp","mz","mx"]:
        L.append(f"  case {nm} => {mem()}")
    L.append("  case fr => janus_frame")
    return "\n".join(("  "*0+ind+l) for l in L)
if __name__=="__main__":
    j=int(sys.argv[1]); print(bullet(j," "*int(sys.argv[2])))
