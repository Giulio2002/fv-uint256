import sys
op=sys.argv[1]
ps=sys.argv[2:]   # pointer names
parts=[]
for p in ps:
    for o in ['','+ 8','+ 16','+ 24']:
        parts.append(f"have := Util.readLE8_lt s.mem ({p}.toNat {o})")
print('; '.join(parts)+f"; simp only [Spec.{op}, Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Util.readLE8_mod]; split <;> (simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; janus_arith)")
