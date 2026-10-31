#!/usr/bin/env python3 -I
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys
M='18446744073709551616'; M2='340282366920938463463374607431768211456'; M3='6277101735386680763835789423207666416102355444464034512896'
def blk(v):
    xs=f"{v}.toNat"
    X0 = (f"N + {M} * s.mem.readLE ({xs} + 8) 8 + {M2} * s.mem.readLE ({xs} + 16) 8 + {M3} * s.mem.readLE ({xs} + 24) 8" if v=='z' else f"s.mem.readLE z.toNat 8 + {M} * s.mem.readLE (z.toNat + 8) 8 + {M2} * s.mem.readLE (z.toNat + 16) 8 + {M3} * s.mem.readLE (z.toNat + 24) 8")
    A=[f"generalize hN : s.mem.readLE {xs} 8 = N at *",
       f"have e1 : N + {M} * s.mem.readLE ({xs} + 8) 8 + {M2} * s.mem.readLE ({xs} + 16) 8 + {M3} * s.mem.readLE ({xs} + 24) 8 = N := (by omega)",
       f"have e2 : Spec.byte (N + {M} * s.mem.readLE ({xs} + 8) 8 + {M2} * s.mem.readLE ({xs} + 16) 8 + {M3} * s.mem.readLE ({xs} + 24) 8) ({X0}) = Spec.byte N ({X0}) := congrArg (fun a => Spec.byte a ({X0})) e1",
       "rw [e2]",
       "rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]",
       f"have hq : ({M} - N / 8 + 3) % {M} = 3 - N / 8 := (by omega)",
       f"have hr : ({M} - 8 * (N % 8) + 56) % {M} % 64 = 8 * (7 - N % 8) := (by omega)",
       "rw [hq, hr]",
       "rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h",
       "· rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]",
       "· rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]",
       "· rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]",
       "· rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]"]
    B=["simp only [Spec.byte]", "split <;> omega"]
    return A,B,B
t=open(ROOT+'/lean/Fv256/Arm64/Neg.lean').read()
t=t.replace('Neg','Byte').replace('(*uint256.Int).Byte(x *Int)','(*uint256.Int).Byte(n *Int)')
t=t.replace('Spec.neg (val256 s.mem x.toNat)','Spec.byte (val256 s.mem x.toNat) (val256 s.mem z.toNat)')
k=t.index("  rcases hzx with rfl | hzx")
k2=t.index("\nnamespace Witness")
def side(v):
    lim="".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o==0 else ' + '+str(o)}); " for p in (('z','x') if v=='x' else ('z',)) for o in (0,8,16,24))
    A,B,_=blk(v)
    out="    simp only [Disjoint] at *\n    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]\n"
    # goals: n<32 ; n>=32 (upper zero) ; upper nonzero  (order from probe: A, B, C)
    out+="    · "+lim+"simp only [Nat.or_eq_zero_iff] at *\n"+"".join("      "+l+"\n" for l in A)
    out+="    · "+lim+"simp only [Nat.or_eq_zero_iff] at *\n"+"".join("      "+l+"\n" for l in B)
    out+="    · "+lim+"simp only [Nat.or_eq_zero_iff] at *\n      simp only [Spec.byte]\n      split <;> omega\n"
    return out
t=t[:k]+"  rcases hzx with rfl | hzx\n  · "+side('z').lstrip()+"  · "+side('x').lstrip()+t[k2:]
t=t.replace("Fv256.Spec.neg` of the number at `x` before the call","Fv256.Spec.byte` of the number at `x` (the index) and the number at `z` before the call").replace("`z = Fv256.Spec.neg x`","`z = byte n of z`")
open(ROOT+'/lean/Fv256/Arm64/Byte.lean','w').write(t)
