import sys; sys.path.insert(0,'/srv/fv-uint256-wBm/tools')
import a64dev as G
A,B=0xb8e08,0xb8e3c
C="x88m56 / 2 ^ 32 % 2 ^ 32 = 2 ^ 31"
W0="(if %s then 2 ^ 64 - 1 else 2 ^ 63 / (x88m56 / 2 ^ 32))" % C
cl=("simp only [setReg, ↓reduceIte, Nat.reduceEqDiff]\n"
    "by_cases hc : %s\n"
    "· first | (exfalso; omega) | (rw [if_pos hc]; try (first | rfl | decide | simp))\n"
    "· first | (exfalso; omega) | (rw [if_neg hc]; try (first | rfl | simp))") % C
G.OVR[(G.off(A),G.off(B))]={('r',0):(W0,cl)}
ex=("have hB' : x88m56 < 18446744073709551616 := hB_x88m56\n"
    "    unfold r0f\n"
    "    by_cases hc : %s\n"
    "    · first | (exfalso; omega) | (have hc2 : x88m56 / 2 ^ 32 = 2 ^ 31 := (by omega)\n"
    "                                  rw [Nat.mod_eq_of_lt hB', if_pos hc, if_pos hc2]; try omega)\n"
    "    · first | (exfalso; omega) | (have hc2 : ¬ (x88m56 / 2 ^ 32 = 2 ^ 31) := (by omega)\n"
    "                                  rw [Nat.mod_eq_of_lt hB', if_neg hc, if_neg hc2]\n"
    "                                  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega)))") % C
G.EXTAC["xbcr0 % 2 ^ 32 = r0f xbcr3"]=ex
G.BNDAC={('r',0):"split <;> first | decide | exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)"}
p=G.do_seg(A,B,skel=(len(sys.argv)<2))
print(p)
