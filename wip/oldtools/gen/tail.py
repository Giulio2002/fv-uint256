import sys
op=sys.argv[1]
b=' '.join(['(Util.readLE8_lt _ _)']*6)
print(f"rw [Util.{op}4 _ _ _ _ _ _ _ _ {b}]; simp [Util.{op}_mod_rd, Nat.{op}_comm]; all_goals simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]")
