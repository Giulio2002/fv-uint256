#!/usr/bin/env python3 -I
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
M='18446744073709551616'; M2='340282366920938463463374607431768211456'; M3='6277101735386680763835789423207666416102355444464034512896'
def blkA(v, div):
    xs=f"{v}.toNat"
    X0 = (f"N + {M} * s.mem.readLE ({xs} + 8) 8 + {M2} * s.mem.readLE ({xs} + 16) 8 + {M3} * s.mem.readLE ({xs} + 24) 8" if v=='z' else f"s.mem.readLE z.toNat 8 + {M} * s.mem.readLE (z.toNat + 8) 8 + {M2} * s.mem.readLE (z.toNat + 16) 8 + {M3} * s.mem.readLE (z.toNat + 24) 8")
    L=[f"generalize hN : s.mem.readLE {xs} 8 = N at *",
       "(try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])",
       f"have e1 : N + {M} * s.mem.readLE ({xs} + 8) 8 + {M2} * s.mem.readLE ({xs} + 16) 8 + {M3} * s.mem.readLE ({xs} + 24) 8 = N := (by omega)",
       f"have e2 : Spec.byte (N + {M} * s.mem.readLE ({xs} + 8) 8 + {M2} * s.mem.readLE ({xs} + 16) 8 + {M3} * s.mem.readLE ({xs} + 24) 8) ({X0}) = Spec.byte N ({X0}) := congrArg (fun a => Spec.byte a ({X0})) e1",
       "rw [e2]",
       "rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]",
       f"have hq : ({M} - (18446744073709551613 + N / 8) % {M}) % {M} = 3 - N / 8 := (by omega)",
       "rw [hq]"]
    if div:
        L+=[f"have hr : ({M} - (18446744073709551560 + N % 8 * 8)) % 64 = 8 * (7 - N % 8) := (by omega)", "rw [hr]"]
    else:
        L+=["have hr7 : N % 8 = 7 := (by omega)", "rw [hr7]"]
    L+=["rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h"]
    for _ in range(4):
        L+=["· rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega"]
    return L
def side(v, kinds):
    lim="".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o==0 else ' + '+str(o)}); " for p in (('z','x') if v=='x' else ('z',)) for o in (0,8,16,24))
    out="    try simp only [Disjoint, Alias] at *\n    janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]\n"
    for kind in kinds:
        if kind=='Adiv': body=blkA(v,True)
        elif kind=='A0': body=blkA(v,False)
        elif kind=='B': body=["(try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])","simp only [Spec.byte]","split <;> omega"]
        else: body=["(try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *)","(try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])","simp only [Spec.byte]","split <;> omega"]
        pre="(try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *); " if kind in ('Adiv','A0','B') else ""
        out+="    · refine ⟨?_, ?_⟩\n      · "+lim+pre+body[0]+"\n"+"".join("        "+l+"\n" for l in body[1:])
        out+="      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]\n"
    return out
t=open(ROOT+'/lean/Fv256/Amd64/Neg.lean').read()
t=t.replace('Neg','Byte')
t=t.replace('Spec.neg (valueAt s x 32)','Spec.byte (valueAt s x 32) (valueAt s z 32)')
k=t.index("  rcases hzx with rfl | hzx")
k2=t.index("\nnamespace Witness")
t=t[:k]+"  rcases hzx with rfl | hzx\n  · "+side('z',['A0','Adiv','C','C']).lstrip()+"  · "+side('x',['A0','Adiv','C','C']).lstrip()+t[k2:]
t=t.replace("set_option maxHeartbeats 8000000 in\n","")
t=t.replace("theorem correctness","set_option maxHeartbeats 8000000 in\ntheorem correctness",1)
t=t.replace('(*uint256.Int).Byte(x *Int) *Int` (amd64): `z = Fv256.Spec.neg x`','(*uint256.Int).Byte(n *Int) *Int` (amd64): `z = the n-th byte (from the most significant end) of z`').replace('is `Fv256.Spec.neg` of the number at `x` before the call','is `Fv256.Spec.byte` of the number at `x` (the index) and the number at `z` before the call')
open(ROOT+'/lean/Fv256/Amd64/Byte.lean','w').write(t)
