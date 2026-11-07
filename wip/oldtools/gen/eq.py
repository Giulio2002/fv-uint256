parts=[f"have := Util.readLE8_lt s.mem ({p}.toNat {o})" for p in ['z','x'] for o in ['','+ 8','+ 16','+ 24']]
print("all_goals ("+'; '.join(parts)+"; simp only [Spec.eq, Util.beq_toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; (repeat' split) <;> first | omega | (simp; omega) | simp_all)")
