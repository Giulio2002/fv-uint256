#!/usr/bin/env python3 -I
# srsh_amd.py : writes lean/Fv256/Proofs/Amd64/SRsh.lean (positive branch reuses the amd64 Rsh handlers)
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
src = open(ROOT + '/tools/gen2/rsh_amd.py').read()
ns = {}
exec(src[src.index("import sys\n") + 11:src.index("def side(")], ns)
M = ns['M']
H = None
def lim4(v):
    return "".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o == 0 else ' + ' + str(o)}); " for p in (('z', 'x') if v == 'x' else ('z',)) for o in (0, 8, 16, 24))
NEG = open(ROOT + '/tools/gen2/srsh_amd_neg.txt').read() if os.path.exists(ROOT + '/tools/gen2/srsh_amd_neg.txt') else None
def indent(lines, k):
    return "".join(" " * k + l + "\n" for l in lines)
def bullet(v, nb):
    Hd = ns['hand'](v)
    a3 = f"(Util.readLE8_lt s.mem ({v}.toNat + 24))"
    a3n = f"(s.mem.readLE ({v}.toNat + 24) 8)"
    out = "· refine ⟨?_, ?_⟩\n"
    out += "  · " + lim4(v) + "generalize hm : n.toNat = m at *\n"
    out += f"    rcases (show {a3n} < 9223372036854775808 ∨ 9223372036854775808 ≤ {a3n} by omega) with hp | hn\n"
    out += f"    · have e := Util.msb_f _ {a3} hp\n      (try simp only [e, eq_self_iff_true, not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true] at *)\n      all_goals\n"
    out += "        rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h\n"
    for k in ['n0', 'g1', 'g2', 'g3', 'g4', 'g5', 'g6']:
        alts = [Hd[k][1:]] if k != 'g6' else [Hd['g6'][1:], Hd['g6a'][1:]]
        out += "        · first\n          | (exfalso; omega)\n"
        for al in alts:
            out += "          | (\n" + indent([f"rw [Util.srsh_pos _ _ (by omega)]"] + al, 14) + "              )\n"
    out += f"    · have e := Util.msb_t _ {a3} hn\n      (try simp only [e, eq_self_iff_true, not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true] at *)\n      all_goals\n"
    out += NEGBLOCK(v, Hd) if NEG is None else NEG.replace('@V@', v)
    out += "  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]\n"
    return out
def NEGBLOCK(v, Hd):
    S, S2 = ns['S'], ns['S2']
    b = [f"(Util.readLE8_lt s.mem ({v}.toNat + {8*i}))" if i else f"(Util.readLE8_lt s.mem {v}.toNat)" for i in range(4)]
    a = [f"s.mem.readLE ({v}.toNat + {8*i}) 8" if i else f"s.mem.readLE {v}.toNat 8" for i in range(4)]
    top = f"rw [Util.top_amd _ m {b[3]} (by omega) (by omega)]"
    neg = "rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]"
    def fin(k, tt):
        L = [f"have e := Util.rsh{k}_t _ _ _ _ {tt} ht {b[0]} {b[1]} {b[2]} {b[3]}"]
        lo = 64 * k
        if k == 0:
            L.append(f"rw [show 256 - {tt} = 192 + (64 - {tt}) from (by omega), Nat.pow_add 2 192 (64 - {tt}), ← e]")
        elif k == 3:
            L.append(f"rw [show 256 - (192 + {tt}) = 64 - {tt} from (by omega), ← e]")
        else:
            L.append(f"rw [show 256 - ({lo} + {tt}) = {192 - lo} + (64 - {tt}) from (by omega), Nat.pow_add 2 {192 - lo} (64 - {tt}), ← e]")
        L += [f"have hP := Util.pw_le {tt} (by omega)", "simp only [Nat.reducePow]"]
        for i in range(1, 4):
            L.append(f"generalize {a[i]} * 2 ^ (64 - {tt}) % {M} = w{i} at *")
        for i in range(4):
            L.append(f"generalize {a[i]} / 2 ^ {tt} = q{i} at *")
        L += [f"generalize 2 ^ (64 - {tt}) = P at *", "omega"]
        return L
    H = []
    H.append(["obtain rfl : m = 0 := (by omega)", neg, "simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one, Nat.sub_self, Nat.add_zero]"])
    H.append(["have ht : m < 64 := (by omega)", top, "simp only [Nat.mod_eq_of_lt ht]",
              f"rw [Util.shrd_val _ _ m ht {b[0]}, Util.shrd_val _ _ m ht {b[1]}, Util.shrd_val _ _ m ht {b[2]}]", neg] + fin(0, 'm'))
    for lit in (64, 128, 192):
        H.append([f"obtain rfl : m = {lit} := (by omega)", neg,
                  f"simp only [{S}, {S2}, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]", "omega"])
    # general t cases, order of ranges: 1..63, 64, 65..127, 128, 129..191, 192, 193..255, >=256
    def g35(base, C, k):
        L = [top,
             f"obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = {base} + t := ⟨m - {base}, (by omega), (by omega), (by omega)⟩",
             f"have hs : ({M} - ({base} + t)) % 64 = 64 - t := (by omega)",
             f"have hm64 : ({base} + t) % 64 = t := (by omega)",
             f"have hc : {M} - ({C} + ({base} + t)) < 64 := (by omega)",
             "simp only [hs, hm64, hc, ite_true]",
             f"simp (disch := omega) only [{S}, {S2}, Util.and_ones_lt, Util.ones_and_lt]"]
        if k == 1:
            L.append(f"rw [Util.shr_or_nat0 _ _ t ht1 ht {b[2]} {b[1]}, Util.shr_or_nat0 _ _ t ht1 ht {b[3]} {b[2]}]")
        else:
            L.append(f"rw [Util.shr_or_nat0 _ _ t ht1 ht {b[3]} {b[2]}]")
        L.append(neg)
        return L + fin(k, 't')
    H3 = g35(64, "18446744073709551488", 1)
    H5 = g35(128, "18446744073709551424", 2)
    H7 = [top, "obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega), (by omega)⟩",
          "have hm64 : (192 + t) % 64 = t := (by omega)",
          "simp only [hm64]", neg] + fin(3, 't')
    Hbig = ["obtain ⟨m', rfl⟩ : ∃ m', m = 256 + m' := ⟨m - 256, (by omega)⟩", "rw [Util.srsh_neg_big _ _ (by omega) (by omega) (by omega)]"]
    order = [(0, H[0]), (1, H[1]), (2, H[2]), (3, H3), (4, H[3]), (5, H5), (6, H[4]), (7, H7), (8, Hbig)]
    out = "        rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ m = 192 ∨ (192 < m ∧ m < 256) ∨ 256 ≤ m by omega) with h | h | h | h | h | h | h | h | h\n"
    for _, hh in order:
        out += "        · first\n          | (exfalso; omega)\n          | (\n" + indent(hh, 14) + "              )\n"
    return out
def blk(v, nb):
    out = "try simp only [Disjoint, Alias] at *\n    janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]\n"
    b = bullet(v, nb)
    for _ in range(nb):
        out += "".join("    " + l + "\n" for l in b.splitlines())
    return out
t = open(ROOT + '/tools/gen2/srsh_amd_head.lean').read()
t = t.replace('@@Z@@', blk('z', 8 + 10).lstrip()).replace('@@X@@', blk('x', 8 + 10).lstrip())
open(ROOT + '/lean/Fv256/Proofs/Amd64/SRsh.lean', 'w').write(t)
