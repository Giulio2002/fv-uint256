#!/usr/bin/env python3
"""Generate the four generic-path compositions of the arm64 AddMod segments (z != m / z = m clone, no overflow / overflow)."""
import sys
PRE_OBT = "obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre"
PRE_TUP = "⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩"
HM = "¬ (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0)"
HNC = "¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8)"
HNOV = "s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 < 2 ^ 256"
HOV = "2 ^ 256 ≤ s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32"

def gen(name, clone, ov):
    L = []
    w = L.append
    ZM = "(hzeq : s.regs 3 = s.regs 0)" if clone else "(hne : s.regs 3 ≠ s.regs 0)"
    ARG = HOV if ov else HNOV
    w(f"set_option maxHeartbeats 64000000 in\nset_option maxRecDepth 200000 in\ntheorem {name} (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)\n    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : {HNC})\n    {ZM}\n    (hm : {HM})\n    ({'hov' if ov else 'hnov'} : {ARG}) :\n    ReachesRet Extracted.program (s.regs 30) s (Post s) := by")
    w(f"  {PRE_OBT}")
    if not clone:
        w("  have hzm' := (hzm.resolve_left (fun h => hne h.symm))")
    w("  have hrod := rod_of_data _ hdata")
    w("  have hm32 : s.mem.readLE (s.regs 3).toNat 32 ≠ 0 := by\n    intro h\n    apply hm\n    have b0 := Util.readLE8_lt s.mem (s.regs 3).toNat\n    have b1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)\n    have b2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)\n    have b3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)\n    rw [Util.readLE_32] at h\n    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega")
    w(f"  refine seg_trans (segA s hpc {PRE_TUP} hnc) ?_")
    w("  intro S1 h1pc q1")
    w("  obtain ⟨r0, r1, r2, r3, r18, r28, r30, r8, sp1, hmem1, hacc1, hx29, hretS, hfr1⟩ := AF_of s S1 hsb hsc q1")
    w("  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega")
    if not clone:
        w("""  refine seg_trans (segB S1 h1pc ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hne
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · rw [r8, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2mem, q2sp, q28, q2r⟩
  have t8 : S2.regs 8 = s.regs 3 := by rw [q28, r3]
  have t8n : (S2.regs 8).toNat = (s.regs 3).toNat := by rw [t8]
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h; rw [q2mem]; exact hmem1 a n h
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2mem]; exact hacc1 a n w
  have hx29_2 : S2.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat := by rw [q2mem]; exact hx29
  have hret_2 : S2.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat := by rw [q2mem]; exact hretS
  have f2 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360)] := by rw [q2mem]; exact hfr1""")
        H2 = "hmem2 _ _ (by omega)"
        FR2 = "[(s.sp.toNat - 376, s.sp.toNat - 360)]"
        SUBR = "(by simp only [Outside, and_true] at h ⊢; omega)"
    else:
        w("""  refine seg_trans (segBc S1 h1pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hzeq
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · omega
  · omega
  · rw [hacc1, sp1n]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [r3, sp1n]; omega
  · rw [r8, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2sp, q2r8, q2r, q2fr, q2val⟩
  have t8n : (S2.regs 8).toNat = s.sp.toNat - 40 := by rw [q2r8]; simp [BitVec.toNat_add]; omega
  rw [sp1n] at q2fr q2val
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → (a + n ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 8 ≤ a) →
      S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h h'
    rw [q2fr.readLE a n (by simp only [Outside, and_true]; omega), hmem1 a n h]
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2fr.accessible, hacc1]
  have hx29_2 : S2.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat := by
    rw [q2fr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hx29
  have hret_2 : S2.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat := by
    rw [q2fr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hretS
  have f2 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360), (s.sp.toNat - 40, s.sp.toNat - 8)] :=
    hfr1.trans q2fr (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  have hclone : S2.mem.readLE (s.sp.toNat - 40) 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    have e : S1.mem.readLE (S1.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
      rw [r3]; exact hmem1 _ _ (by omega)
    have := q2val
    rw [e] at this
    have e2 : s.sp.toNat - 368 + 328 = s.sp.toNat - 40 := by omega
    rw [e2] at this
    exact this""")
        H2 = "hmem2 _ _ (by omega) (by omega)"
        FR2 = "[(s.sp.toNat - 376, s.sp.toNat - 360), (s.sp.toNat - 40, s.sp.toNat - 8)]"
        SUBR = "(by simp only [Outside, and_true] at h ⊢; omega)"
    # regs of S2
    w("""  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t18 : S2.regs 18 = s.regs 18 := by rw [q2r 18 (by decide) (by decide) (by decide), r18]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have sp2 : S2.sp = s.sp - 368 := by rw [q2sp, sp1]
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [sp2]; simp [BitVec.toNat_sub]; omega""".replace("(by decide) (by decide) (by decide)", "(by decide) (by decide) (by decide)") if not clone else """  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t18 : S2.regs 18 = s.regs 18 := by rw [q2r 18 (by decide) (by decide) (by decide), r18]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have sp2 : S2.sp = s.sp - 368 := by rw [q2sp, sp1]
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [sp2]; simp [BitVec.toNat_sub]; omega""")
    # segC / segCov
    seg = "segCov" if ov else "segC"
    HN = "hov" if ov else "hnov"
    w(f"""  refine seg_trans ({seg} S2 h2pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [t0]; exact hzb
  · rw [t0, hacc2]; exact hza
  · rw [t1]; exact hxb
  · rw [t1, hacc2]; exact hxa
  · rw [t2]; exact hyb
  · rw [t2, hacc2]; exact hya
  · rw [t0, t1]; exact hzx
  · rw [t0, t2]; exact hzy
  · rw [t1, t2, {H2}, {H2}]; exact {HN}
  intro S3 h3pc ⟨q3pc, q3sp, q3r, q3frame, q3val⟩""")
    w("""  have sp3 : S3.sp = s.sp - 368 := by rw [q3sp, sp2]
  have sp3n : S3.sp.toNat = s.sp.toNat - 368 := by rw [sp3]; simp [BitVec.toNat_sub]; omega
  have u0 : S3.regs 0 = s.regs 0 := by rw [q3r 0 (by decide) (by decide), t0]
  have u8 : (S3.regs 8).toNat = (S2.regs 8).toNat := by rw [q3r 8 (by decide) (by decide)]
  have u18 : S3.regs 18 = s.regs 18 := by rw [q3r 18 (by decide) (by decide), t18]
  have u28 : S3.regs 28 = s.regs 28 := by rw [q3r 28 (by decide) (by decide), t28]
  have hmem3 : ∀ a n, ((a + n ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ a)) → S3.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h
    apply q3frame.readLE
    simp only [Outside, and_true]; rw [t0]; exact h
  have hacc3 : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q3frame.accessible, hacc2]
  have hx29_3 : S3.mem.readLE (S3.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]
    have e : s.sp.toNat - 368 - 8 = s.sp.toNat - 376 := by omega
    rw [e]; exact hx29_2
  have hret_3 : S3.mem.readLE S3.sp.toNat 8 = (s.regs 30).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]; exact hret_2""")
    # m' pointer, content
    if not clone:
        w("""  have mptr : (S3.regs 8).toNat = (s.regs 3).toNat := by rw [u8, t8n]
  have mval : S3.mem.readLE (S3.regs 8).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [mptr, hmem3 _ _ (by omega), hmem2 _ _ (by omega)]""")
    else:
        w("""  have mptr : (S3.regs 8).toNat = s.sp.toNat - 40 := by rw [u8, t8n]
  have mval : S3.mem.readLE (S3.regs 8).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [mptr, hmem3 _ _ (by omega)]; exact hclone""")
    # value of z after segC
    if not ov:
        w(f"""  have vz : S3.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
    have := q3val
    rw [t0, t1, t2] at this
    rw [this, {H2}, {H2}]""")
    else:
        w(f"""  have vz : S3.mem.readLE (s.regs 0).toNat 32 + 2 ^ 256 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
    have := q3val
    rw [t0, t1, t2] at this
    rw [this, {H2}, {H2}]""")
    # frames so far
    w(f"""  have f3 : MemFrame s.mem S3.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)] := by
    rw [t0] at q3frame
    exact f2.trans q3frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)""")
    # final segment
    G3 = f"rw [u28, hmem3 ((s.regs 28).toNat + 16) 8 (by omega), {H2.replace('_ _', '((s.regs 28).toNat + 16) 8')}]; omega"
    if not ov:
        HMB = "rw [mptr]; omega" if clone else "rw [mptr]; exact hmb"
        HMA = "rw [hacc3, mptr]; exact s.mem.accessible_sub hsw (Or.inl rfl) (by omega) (by omega)" if clone else "rw [hacc3, mptr]; exact hma"
        w(f"""  refine seg_mono (segD S3 (s.regs 30) (s.regs 29) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · rw [hacc3]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [u28]; exact hg1
  · rw [u28, hacc3]; exact hg2
  · {G3}
  · rw [u28]; omega
  · rw [u0]; exact hzb
  · rw [u0, hacc3]; exact hza
  · {HMB}
  · {HMA}
  · rw [u0]; omega
  · rw [mptr]; omega
  · exact hret_3
  · exact h30a
  · exact h30b
  · exact hx29_3
  intro S4 ⟨q4pc, q4sp, q40, q428, q429, q418, q430, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, q429, q430, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q418, u18]
  · rw [q428, u28]
  · rw [u0, mval, vz] at q4val
    rw [q4val]
    simp [Fv256.F.addmodSpec, Fv256.B.modSpec]
  · rw [u0, sp3n] at q4frame
    exact f3.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)""")
    else:
        HDM = "rw [mptr]; omega"
        HMB = "rw [mptr]; omega" if clone else "rw [mptr]; exact hmb"
        HMA = "rw [hacc3, mptr]; exact s.mem.accessible_sub hsw (Or.inl rfl) (by omega) (by omega)" if clone else "rw [hacc3, mptr]; exact hma"
        w(f"""  refine seg_mono (segEF S3 (s.regs 30) (s.regs 29) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · rw [hacc3]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [hacc3]; exact hrod
  · rw [u28]; exact hg1
  · rw [u28, hacc3]; exact hg2
  · {G3}
  · rw [u28, sp3n]; omega
  · rw [u0]; exact hzb
  · rw [u0, hacc3]; exact hza
  · {HMB}
  · {HMA}
  · rw [u0, sp3n]; omega
  · rw [mptr, sp3n]; omega
  · rw [mptr, u0]; omega
  · rw [mval]; exact hm32
  · exact hret_3
  · exact h30a
  · exact h30b
  · exact hx29_3
  intro S4 ⟨q4pc, q4sp, q40, q428, q429, q418, q430, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, q429, q430, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q418, u18]
  · rw [q428, u28]
  · rw [u0, mval, vz] at q4val
    rw [q4val]
    simp [Fv256.F.addmodSpec, hm32]
  · rw [u0, sp3n] at q4frame
    exact f3.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)""")
    w("")
    return "\n".join(L)

if __name__ == "__main__":
    out = sys.argv[1]
    t = open(out).read()
    marker = "end Fv256.Arm64.AddModComp2"
    body = "\n".join(gen(n, c, o) for n, c, o in (("gb_nov", False, False), ("gb_ov", False, True), ("ga_nov", True, False), ("ga_ov", True, True)))
    t = t.replace(marker, body + "\n" + marker)
    open(out, "w").write(t)
