#!/usr/bin/env python3 -I
# srsh_arm.py : writes lean/Fv256/Arm64/SRsh.lean (positive branch reuses the Rsh handlers; negative branch uses x>>n + (2^256 - 2^(256-n)))
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
M = '18446744073709551616'
OW = "by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]"
def common(v):
    b = [f"(Util.readLE8_lt s.mem ({v}.toNat + {8*i}))" if i else f"(Util.readLE8_lt s.mem {v}.toNat)" for i in range(4)]
    lim = "".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o == 0 else ' + ' + str(o)}); " for p in (('z', 'x') if v == 'x' else ('z',)) for o in (0, 8, 16, 24))
    a = [f"s.mem.readLE ({v}.toNat + {8*i}) 8" if i else f"s.mem.readLE {v}.toNat 8" for i in range(4)]
    return b, lim, a
def pos_cases(v):
    b, lim, a = common(v)
    src = open(ROOT + '/tools/gen2/rsh_arm.py').read()
    ns = {}
    exec("M = '%s'\n" % M + src[src.index('def lim('):src.index('def block(')], ns)
    hs = ns['hand'](v)
    names = ["_ hsg", "_ hsg _", "_ hsg _ _", "_ hsg _ _ _", "_ hsg _ _ _"]
    out = []
    for h, nm in zip(hs, names):
        L = ["· rename_i " + nm,
             "  " + lim,
             "  refine ⟨?_, " + OW + "⟩",
             f"  rw [Util.srsh_pos _ _ (by have := Util.msb_pos _ {b[3]} hsg; omega)]"]
        L += ["  " + h[0]] + ["  " + l for l in h[1:]]
        out.append(L)
    return out
def neg_cases(v):
    b, lim, a = common(v)
    head = lambda nm: ["· rename_i " + nm, "  " + lim, "  refine ⟨?_, " + OW + "⟩", f"  have hs3 := Util.msb_neg _ {b[3]} hsg", "  generalize hm : n.toNat = m at *"]
    out = []
    out.append(head("_ hsg") + ["  obtain rfl : m = 0 := (by clear hsg; omega)",
                "  rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]",
                "  simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one, Nat.sub_self, Nat.add_zero]"])
    out.append(head("_ hsg _") + ["  rw [Util.srsh_neg_big _ _ (by omega) (by omega) (by omega)]"])
    def case(k, nm):
        L = head(nm)
        if k == 0:
            L += ["  have ht1 : 1 ≤ m := (by omega)", "  have ht : m < 64 := (by clear hsg; omega)",
                  f"  have hc2 : {M} - m - 18446744073709551552 = 64 - m := (by clear hsg; omega)",
                  "  simp only [hc2, Nat.mod_eq_of_lt ht]",
                  f"  rw [Util.shr_or_nat _ _ m ht1 ht {b[1]} {b[0]}, Util.shr_or_nat _ _ m ht1 ht {b[2]} {b[1]}, Util.shr_or_nat _ _ m ht1 ht {b[3]} {b[2]}]",
                  f"  rw [Util.top_val _ m {b[3]} ht]",
                  "  rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]",
                  f"  have e := Util.rsh0_t _ _ _ _ m ht {b[0]} {b[1]} {b[2]} {b[3]}",
                  "  rw [show 256 - m = 192 + (64 - m) from (by omega), Nat.pow_add, ← e]",
                  "  have hP := Util.pw_le m (by omega)", "  simp only [Nat.reducePow]"]
            tt = 'm'
        else:
            lo = 64 * k
            c3 = 2**64 - 64 - lo
            L += [f"  obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = {lo} + t := ⟨m - {lo}, (by omega), (by omega)⟩",
                  f"  have hc : {M} - ({lo} + t) - {c3} = 64 - t := Util.sub_aux {lo} t ht (by omega)",
                  f"  have hp : ({lo} + t - {lo}) % 64 = t := (by clear hsg; omega)",
                  f"  have hq : ({lo} + t) % 64 = t := (by clear hsg; omega)",
                  f"  have hc1 : ({M} - t + 64) % {M} = 64 - t := (by clear hsg; omega)",
                  f"  have hc2 : {M} - t - 18446744073709551552 = 64 - t := Util.sub_aux2 t ht",
                  "  simp only [hp, hq, hc1, hc2, hc]"]
            nlow = 3 - k
            if nlow > 0:
                L += ["  rw [" + ", ".join(f"Util.shr_or_bv _ _ t ht {b[i+k+1]} {b[i+k]}" for i in range(nlow)) + "]"]
            L += [f"  rw [Util.top_val _ t {b[3]} ht]",
                  "  rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]",
                  f"  have e := Util.rsh{k}_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}",
                  (f"  rw [show 256 - ({lo} + t) = 64 - t from (by omega), ← e]" if lo == 192 else f"  rw [show 256 - ({lo} + t) = {192 - lo} + (64 - t) from (by omega), Nat.pow_add 2 {192 - lo} (64 - t), ← e]"),
                  "  have hP := Util.pw_le t (by omega)", "  simp only [Nat.reducePow]"]
            tt = 't'
        for i in range(1, 4):
            L.append(f"  generalize {a[i]} * 2 ^ (64 - {tt}) % {M} = w{i} at *")
        for i in range(4):
            L.append(f"  generalize {a[i]} / 2 ^ {tt} = q{i} at *")
        L += [f"  generalize 2 ^ (64 - {tt}) = P at *", "  omega"]
        return L
    out.append(case(3, "_ hsg _ _"))
    out.append(case(2, "_ hsg _ _ _"))
    out.append(case(0, "_ hsg _ _ _ _"))
    out.append(case(1, "_ hsg _ _ _ _"))
    return out
def block(v):
    out = "    simp only [Disjoint] at *\n    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]\n"
    for L in pos_cases(v) + neg_cases(v):
        out += "".join("    " + l + "\n" for l in L)
    return out
t = open(ROOT + '/tools/gen2/srsh_head.lean').read()
t = t.replace('@@Z@@', block('z').lstrip()).replace('@@X@@', block('x').lstrip())
open(ROOT + '/lean/Fv256/Arm64/SRsh.lean', 'w').write(t)
