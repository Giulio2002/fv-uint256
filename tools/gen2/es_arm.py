#!/usr/bin/env python3 -I
# es_arm.py : writes lean/Fv256/Arm64/ExtendSign.lean (from es_arm_head.lean)
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
def rd(p, o): return f"s.mem.readLE ({p}.toNat + {o}) 8" if o else f"s.mem.readLE {p}.toNat 8"
def lt(p, o): return f"(Util.readLE8_lt s.mem ({p}.toNat + {o}))" if o else f"(Util.readLE8_lt s.mem {p}.toNat)"
def ind(lines, k): return [" " * k + l for l in lines]
def goal_i(X, Y, i):
    LL = [lt(X, 8 * j) for j in range(4)]
    L = []
    L += [f"have := {LL[j]}" for j in range(4)] + [f"have := {lt(Y, 0)}"]
    L += ["obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›",
          "simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]",
          f"generalize hb : {rd(Y, 0)} = b0 at *"]
    ks = [k for k in range(8 * i, 8 * i + 8) if k <= 30]
    L += ["rcases (show " + " ∨ ".join(f"b0 = {k}" for k in ks) + " by omega) with " + " | ".join(["h"] * len(ks))]
    for k in ks:
        sh = 8 * (k % 8)
        S = f"((((BitVec.ofNat 64 {k}).rotateRight 61).toNat &&& 56) % 64)"
        body = [f"obtain rfl : b0 = {k} := h",
                f"have hsh : {S} = {sh} := by decide",
                f"(try simp only [hsh])",
                *([f"have hsh0 : (((0#64).rotateRight 61).toNat &&& 56) % 64 = 0 := by decide", "(try simp only [hsh0])"] if k == 0 else []),
                f"rw [Util.es_E _ {sh} (by omega) (by omega)]"]
        if i < 3:
            body += [f"rw [Util.es_F _ {sh} (by omega) (by omega)]"]
        body += [f"simp only [Spec.extendSign, show {k} < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]",
                 "(try split) <;> (try split) <;> (try split) <;> omega"]
        L += ["· " + body[0]] + ind(body[1:], 2)
    return L
def goals(X, Y):
    G = []
    LL = [lt(X, 8 * j) for j in range(4)]
    # 0: b0 > 30
    G.append(["have := " + LL[0], "simp only [Spec.extendSign]", "rw [if_neg (by omega)]"])
    for i in range(4):
        G.append(goal_i(X, Y, i))
    # 5: y hi nonzero
    G.append([f"have := {LL[0]}", f"have := {LL[1]}", f"have := {LL[2]}", f"have := {LL[3]}",
              f"have := {lt(Y, 0)}", f"have := {lt(Y, 8)}", f"have := {lt(Y, 16)}", f"have := {lt(Y, 24)}",
              "simp only [Spec.extendSign]", "rw [if_neg]",
              "rcases Util.or3_ne _ _ _ ‹¬ _ ||| (_ ||| _) = 0› with h | h | h <;> omega"])
    return G
def block(X, Y):
    out = ["simp only [Disjoint] at *",
           "janus_run [Util.rot3_idx', Util.readLE8_mod]"]
    for g in goals(X, Y):
        out += ["· " + g[0]] + ind(g[1:], 2)
    return out
CONFIGS = {'A': ('z', 'z'), 'B': ('z', 'y'), 'C': ('x', 'z'), 'D': ('x', 'x'), 'E': ('x', 'y')}
t = open(ROOT + '/tools/gen2/es_arm_head.lean').read()
for c, (X, Y) in CONFIGS.items():
    col = 8 if c in 'DE' else 6
    t = t.replace('@@' + c + '@@', "\n".join(ind(block(X, Y), col)).lstrip())
open(ROOT + '/lean/Fv256/Arm64/ExtendSign.lean', 'w').write(t)
