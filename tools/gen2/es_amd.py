#!/usr/bin/env python3 -I
# es_amd.py : writes lean/Fv256/Proofs/Amd64/ExtendSign.lean (from es_amd_head.lean)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
def rd(p, o): return f"s.mem.readLE ({p}.toNat + {o}) 8" if o else f"s.mem.readLE {p}.toNat 8"
def lt(p, o): return f"(Util.readLE8_lt s.mem ({p}.toNat + {o}))" if o else f"(Util.readLE8_lt s.mem {p}.toNat)"
def ind(lines, k): return [" " * k + l for l in lines]
def bullet(X, Y):
    LL = [lt(X, 8 * j) for j in range(4)]
    YL = [lt(Y, 8 * j) for j in range(4)]
    y = [rd(Y, 8 * j) for j in range(4)]
    L = ["· refine ⟨?_, ?_⟩",
         "  · " + "".join(f"have := {t}; " for t in LL + YL).rstrip(),
         f"    have hbv := Util.bvor3 _ _ _ {YL[1]} {YL[2]} {YL[3]}",
         "    (try simp only [hbv, Util.or3l_iff] at *)",
         "    all_goals",
         f"      generalize hb : {y[0]} = b0 at *",
         f"      rcases (show ({y[1]} = 0 ∧ {y[2]} = 0 ∧ {y[3]} = 0) ∨ (0 < {y[1]} ∨ 0 < {y[2]} ∨ 0 < {y[3]}) by omega) with hz0 | hnz",
         "      · obtain ⟨hy1, hy2, hy3⟩ := hz0",
         "        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]",
         "        rcases (show " + " ∨ ".join(f"b0 = {k}" for k in range(31)) + " ∨ 31 ≤ b0 by omega) with " + " | ".join(["h"] * 32)]
    for k in range(31):
        sh = 8 * (k % 8)
        body = [f"obtain rfl : b0 = {k} := h"]
        if k % 8 == 0:
            body += ["rw [Util.es_Ea0 _ (by omega)]", "(try rw [Util.es_Fa0 _ (by omega)])"]
        else:
            body += ["simp only [Nat.reduceMod, Nat.reduceMul]",
                     f"rw [Util.es_Ea _ {sh} (by omega) (by omega)]", f"(try rw [Util.es_Fa _ {sh} (by omega)])"]
        body += [f"simp only [Spec.extendSign, show {k} < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]",
                 "(try split) <;> (try split) <;> (try split) <;> omega"]
        L += ["        · first", "          | (exfalso; omega)", "          | ("] + ind(body, 14) + ["            )"]
    L += ["        · first", "          | (exfalso; omega)", "          | (",
          "              simp only [Spec.extendSign]", "              rw [if_neg (by omega)]", "            )",
          "      · first", "        | (exfalso; omega)", "        | (",
          "            simp only [Spec.extendSign]", "            rw [if_neg (by omega)]", "          )",
          "  · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]"]
    return L
def block(X, Y):
    out = ["try simp only [Disjoint, Alias] at *",
           "janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]"]
    b = bullet(X, Y)
    for _ in range(10):
        out += b
    return out
CONFIGS = {'A': ('z', 'z'), 'B': ('z', 'y'), 'C': ('x', 'z'), 'D': ('x', 'x'), 'E': ('x', 'y')}
t = open(ROOT + '/tools/gen2/es_amd_head.lean').read()
for c, (X, Y) in CONFIGS.items():
    col = 8 if c in 'DE' else 6
    t = t.replace('@@' + c + '@@', "\n".join(ind(block(X, Y), col)).lstrip())
open(ROOT + '/lean/Fv256/Proofs/Amd64/ExtendSign.lean', 'w').write(t)
