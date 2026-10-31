#!/usr/bin/env python3 -I
# rsh_amd.py [debug] : writes lean/Fv256/Amd64/Rsh.lean
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys
M='18446744073709551616'
S="BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero"
S2="Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero"
def lim(v,i): return f"(Util.readLE8_lt s.mem ({v}.toNat + {8*i}))" if i else f"(Util.readLE8_lt s.mem {v}.toNat)"
def hand(v):
    b=[lim(v,i) for i in range(4)]
    pre=["generalize hm : n.toNat = m at *"]
    def args(t): return f"_ _ _ _ {t} ht {b[0]} {b[1]} {b[2]} {b[3]}"
    H={}
    H['n0']=pre+["obtain rfl : m = 0 := (by omega)","simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]"]
    H['g1']=pre+["have ht : m < 64 := (by omega)","simp only [Nat.mod_eq_of_lt ht]",
        f"rw [Util.shrd_val _ _ m ht {b[0]}, Util.shrd_val _ _ m ht {b[1]}, Util.shrd_val _ _ m ht {b[2]}]",
        f"rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]})]",
        "simp only [Spec.rsh]", f"exact Util.rsh0_t _ _ _ _ m ht {b[0]} {b[1]} {b[2]} {b[3]}"]
    H['g2']=pre+["obtain rfl : m = 64 := (by omega)",f"simp only [{S}, {S2}, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]","omega"]
    H['g4']=pre+["obtain rfl : m = 128 := (by omega)",f"simp only [{S}, {S2}, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]","omega"]
    def g35(base, C, kind):
        L=[f"obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = {base} + t := ⟨m - {base}, (by omega), (by omega), (by omega)⟩",
           f"have hs : ({M} - ({base} + t)) % 64 = 64 - t := (by omega)",
           f"have hm64 : ({base} + t) % 64 = t := (by omega)",
           f"have hc : {M} - ({C} + ({base} + t)) < 64 := (by omega)",
           "simp only [hs, hm64, hc, ite_true]",
           f"simp (disch := omega) only [{S}, {S2}, Util.and_ones_lt, Util.ones_and_lt]"]
        if kind==1:
            L+=[f"rw [Util.shr_or_nat0 _ _ t ht1 ht {b[2]} {b[1]}, Util.shr_or_nat0 _ _ t ht1 ht {b[3]} {b[2]}]",
                f"rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]})]",
                "simp only [Spec.rsh]", f"exact Util.rsh1_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}"]
        else:
            L+=[f"rw [Util.shr_or_nat0 _ _ t ht1 ht {b[3]} {b[2]}]",
                f"rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]})]",
                "simp only [Spec.rsh]", f"exact Util.rsh2_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}"]
        return L
    H['g3']=pre+g35(64,"18446744073709551488",1)
    H['g5']=pre+g35(128,"18446744073709551424",2)
    x3 = f"(s.mem.readLE ({v}.toNat + 24) 8)"
    H['g6']=pre+["by_cases hlt : m - 192 < 64",
        "· obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩",
        "  have hq : 192 + t - 192 = t := (by omega)",
        "  have hm : (192 + t) % 64 = t := (by omega)",
        f"  have hd : {x3} / 2 ^ t < {M} := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]}",
        f"  simp (disch := omega) only [hq, hm, ht, ite_true, {S}, {S2}, Util.and_ones_lt, Util.ones_and_lt]",
        "  rw [Nat.mod_eq_of_lt hd]",
        "  simp only [Spec.rsh]",
        f"  exact Util.rsh3_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}",
        "· simp only [if_neg hlt]",
        f"  simp only [{S}, {S2}, Spec.rsh]",
        f"  rw [Util.rsh_big _ _ (by have := {b[0]}; have := {b[1]}; have := {b[2]}; have := {b[3]}; omega) (by omega)]",
        "  try omega"]
    H['g6a']=pre+["by_cases hlt : m - 192 < 64",
        "· obtain rfl : m = 192 := (by omega)",
        f"  simp (disch := omega) only [{S}, {S2}, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]",
        f"  (try rw [Nat.mod_eq_of_lt {b[3]}])",
        "  omega",
        "· simp only [if_neg hlt]",
        f"  simp only [{S}, {S2}, Spec.rsh]",
        f"  rw [Util.rsh_big _ _ (by have := {b[0]}; have := {b[1]}; have := {b[2]}; have := {b[3]}; omega) (by omega)]",
        "  try omega"]
    return H
def side(v,order=None):
    H=hand(v)
    lim_="".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o==0 else ' + '+str(o)}); " for p in (('z','x') if v=='x' else ('z',)) for o in (0,8,16,24))
    out="    try simp only [Disjoint, Alias] at *\n    janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]\n"
    ks=['n0','g1','g2','g3','g4','g5','g6','g7']
    # 8 goals possible; each bullet dispatches on m by itself
    return out, H, lim_, ks
def bullet(v, nb):
    out,H,lim_,ks=side(v)
    # nb bullets, all identical dispatchers
    body="    · refine ⟨?_, ?_⟩\n      · "+lim_+"generalize hm : n.toNat = m at *\n"
    body+="        rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h\n"
    for k in ks[:7]:
        pass
    for k,hk in zip(['n0','g1','g2','g3','g4','g5','g67'],range(7)):
        hh=H[k if k!='g67' else 'g6']
        lines=hh[1:]
        body+="        · first | (exfalso; omega) | (\n"+"".join("            "+l+"\n" for l in lines)+"            )\n"
    body+="      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]\n"
    return out+body*nb
t=open(ROOT+'/lean/Fv256/Amd64/Neg.lean').read()
t=t.replace('Neg','Rsh').replace('(z x : BitVec 64)','(z x n : BitVec 64)').replace('[z, x]','[z, x, n]')
t=t.replace('Spec.neg (valueAt s x 32)','Spec.rsh (valueAt s x 32) n.toNat')
t=t.replace("theorem correctness","set_option maxHeartbeats 16000000 in\ntheorem correctness",1)
k=t.index("  rcases hzx with rfl | hzx")
k2=t.index("\nnamespace Witness")
orderA=['g1','g2','g3','g4','g5','g6','g7']
orderD=['n0','g1','g2','g3','g4','g5','g6','g7']
def blk(v,nb):
    out,H,lim_,ks=side(v)
    body=""
    for _ in range(nb):
        body+="    · refine ⟨?_, ?_⟩\n      · "+lim_+"generalize hm : n.toNat = m at *\n"
        body+="        rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h\n"
        for k in ['n0','g1','g2','g3','g4','g5','g6']:
            lines=H[k][1:]
            alts=[lines]
            if k=='g6': alts=[H['g6'][1:], H['g6a'][1:]]
            body+="        · first\n          | (exfalso; omega)\n"
            for al in alts:
                body+="          | (\n"+"".join("              "+l+"\n" for l in al)+"              )\n"
        body+="      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]\n"
    return out+body
t=t[:k]+"  rcases hzx with rfl | hzx\n  · "+blk('z',8).lstrip()+"  · "+blk('x',8).lstrip()+t[k2:]
t=t.replace("def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)","def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)\ndef n : BitVec 64 := 0#64")
t=t.replace("if i = 3 then x else if i = 4","if i = 3 then x else if i = 1 then n else if i = 4")
t=t.replace("rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩","rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩")
t=t.replace("⟨ret, s0, z, x, hret, setup, hpre⟩","⟨ret, s0, z, x, n, hret, setup, hpre⟩").replace("correctness z x ret hret s0 setup hpre","correctness z x n ret hret s0 setup hpre")
t=t.replace('(*uint256.Int).Rsh(x *Int) *Int` (amd64): `z = Fv256.Spec.neg x`','(*uint256.Int).Rsh(x *Int, n uint) *Int` (amd64): `z = x >> n`').replace('is `Fv256.Spec.neg` of the number at `x` before the call','is `Fv256.Spec.rsh` of the number at `x`, shifted right by `n` (`RCX`, any 64-bit value), before the call').replace('it returns `z` holding `0`','it returns `z` holding the shifted value of `x`')
open(ROOT+'/lean/Fv256/Amd64/Rsh.lean','w').write(t)
