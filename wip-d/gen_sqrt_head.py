#!/usr/bin/env python3
"""bullets for the three head goals of sqrt_big (limb j = 1,2,3 holds the top bit)"""
import sys
def XR(i): return f"s.mem.readLE ((s.regs 3).toNat + {8*i}) 8" if i else "s.mem.readLE (s.regs 3).toNat 8"
LIT=["","","340282366920938463463374607431768211456","6277101735386680763835789423207666416102355444464034512896"]
def bullet(j, upto):
    ZRW="".join(f"rw [hz{i}]; " for i in range(j+1,4))
    c=64*j+2
    zs=list(range(j+1,4))
    L=[]
    L.append(f"  · have hl0 := Util.readLE8_lt s.mem (s.regs 3).toNat")
    L.append(f"    have hl1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)")
    L.append(f"    have hl2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)")
    L.append(f"    have hl3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)")
    for i in zs:
        L.append(f"    have hz{i} : {XR(i)} = 0 := by janus_assumption")
    L.append(f"    have hxj : {XR(j)} ≠ 0 := (show ¬ {XR(j)} = 0 by janus_assumption)")
    L.append(f"    obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 ({XR(j)}) = k := ⟨_, rfl⟩")
    args=" ".join("("+XR(i)+")" for i in range(j+1))
    lims=" ".join(f"hl{i}" for i in range(j+1))
    L.append(f"    have hbl := Fv256.B.f64_bl{j} {args} k {lims} hxj hk")
    L.append(f"    have hkj : k < 64 := by have := Util.clz_bl 64 ({XR(j)}) hl{j}; have := SqrtHead.bl_pos _ hxj; omega")
    L.append(f"    rw [hk] at hLv hRv")
    L.append(f"    have hcl : ((BitVec.ofNat 64 (63 - k) + {c}#64) >>> 1).toNat = (63 - k + {c}) / 2 := SqrtHead.shr1_add (63 - k) {c} (by omega)")
    L.append(f"    rw [hcl] at hLv hRv")
    L.append(f"    have harith := SqrtHead.head_arith _ ({64*j+64} - k) ((63 - k + {c}) / 2) hbl (by omega) (by omega) (by omega)")
    n=f"((63 - k + {c}) / 2)"
    L += [
    "    obtain ⟨hc1, hc128, hXinv, hX64, hX256⟩ := harith",
    "    simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, show (256 : Nat) ^ 8 = 2 ^ 64 by decide,",
    "      Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)] at hLv",
    f"    have hlsh : Spec.lsh 1 {n} = 2 ^ {n} := by",
    "      unfold Spec.lsh Spec.W",
    "      rw [Nat.one_mul]",
    "      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))",
    "    rw [hlsh] at hLv",
    "    simp (disch := (simp [Outside]; omega)) only [hLf.readLE] at hRv",
    "    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,",
    "      Janus.Arm64.Memory.readLE_writeLE_inside] at hRv",
    f"    have hsumA : s'.mem.readLE ((s.regs 4).toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 +",
    f"        2 ^ 128 * s'.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE ((s.regs 4).toNat - 40 + 24) 8 = 2 ^ {n} := by",
    "      rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),",
    "        hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]",
    "      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,",
    "        Janus.Arm64.Memory.readLE_writeLE_inside]",
    "      exact hLv",
    "    have hXeq : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by",
    "      rw [Util.readLE_32]",
    "    have hr0 : s'.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 64 := Util.readLE8_lt _ _",
    "    grab_proj_of hRf regs 4 as hs4",
    "    grab_proj_of hRf regs 5 as hs5",
    "    grab_proj_of hRf regs 14 as hs14",
    "    grab_proj_of hRf xmm 15 as hsx",
    "    grab_proj_of hLf regs 14 as hl14",
    "    grab_proj_of hLf regs 5 as hl5",
    "    grab_proj_of hLf xmm 15 as hlx",
    "    have hXs : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 2 ^ 128 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by",
    "      rw [Util.readLE_32]",
    "    have f1 : (s.regs 4).toNat - 72 + 8 = (s.regs 4).toNat - 64 := by omega",
    "    have f2 : (s.regs 4).toNat - 72 + 16 = (s.regs 4).toNat - 56 := by omega",
    "    have f3 : (s.regs 4).toNat - 72 + 24 = (s.regs 4).toNat - 48 := by omega",
    "    have g1 : (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 := by omega",
    "    have g2 : (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 := by omega",
    "    have g3 : (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 := by omega",
    "    simp only [f1, f2, f3, ← hXs, Spec.rsh] at hRv",
    "    simp only [g1, g2, g3] at hsumA",
    "    refine big_loop s (s.mem.readLE (s.regs 3).toNat 32) (s.regs 0) (s.regs 3) (SPost s) (by omega) (by omega) hra2 hdz hdx hdg hgb hnw2 hgr hsp (by omega)",
    "      (fun r S' hsq h0 h4 h5 h14 hx15' hdf hmx hr hfr => ⟨h0, h4, h5, h14, by rw [hx15', hx15], hdf, hmx, by rw [hr]; exact hsq, hfr⟩)",
    f"      (2 ^ {n}) (s'.mem.readLE ((s.regs 4).toNat - 40) 8) (s'.mem.readLE ((s.regs 4).toNat - 32) 8) (s'.mem.readLE ((s.regs 4).toNat - 24) 8) (s'.mem.readLE ((s.regs 4).toNat - 16) 8)",
    "      (s'.mem.readLE ((s.regs 4).toNat - 72) 8) (s'.mem.readLE ((s.regs 4).toNat - 64) 8) (s'.mem.readLE ((s.regs 4).toNat - 56) 8) (s'.mem.readLE ((s.regs 4).toNat - 48) 8)",
    "      _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) (by rw [hXeq]; ZRW exact hXinv) ?hXm",
    "    case hXm =>",
    "      rw [Util.readLE_32]",
    "      simp (disch := (simp [Outside]; omega)) only [hRf.readLE]",
    "      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,",
    "        Janus.Arm64.Memory.readLE_writeLE_inside]",
    "      simp (disch := (simp [Outside]; omega)) only [hLf.readLE]",
    "      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,",
    "        Janus.Arm64.Memory.readLE_writeLE_inside]",
    "      exact hXs.symm",
    "    case inv =>",
    "      refine ⟨?rip, ?r4, ?r5, ?r14, ?x15, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?msav, ?mz, ?mx,",
    "        Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,",
    "        Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?hwin, ?hxacc, ?hzacc, hzw, hxw, ?hfrm⟩",
    "      case rip => show (4957573#64 : BitVec 64) = BitVec.ofNat 64 headB; decide",
    "      case r4 => rw [hs4]; simp [setRegF, sub144]",
    "      case r5 => rw [hs5]; simp [setRegF, hl5]",
    "      case r14 => rw [hs14]; simp [setRegF, hl14]",
    "      case x15 => rw [hsx]; simp [hlx, hx15]",
    "      case mret => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]",
    "      case msav => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 5); omega",
    "      case mz => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 0); omega",
    "      case mx => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 3); omega",
    "      case hwin => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc",
    "      case hxacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hx",
    "      case hzacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hz",
    "      case hfrm =>",
    "        refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)])",
    "          (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?AJJ hLf ?s1JJ)",
    "          (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?BJJ hRf ?s2JJ) ?s3JJ",
    "        · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)",
    "        · intro a n h; simp [Outside] at h ⊢; omega",
    "        · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)",
    "        · intro a n h; simp [Outside] at h ⊢; omega",
    "        · intro a n h; simp [Outside] at h ⊢; omega"]
    return "\n".join(L).replace("ZRW", ZRW).replace("JJ", str(j))
