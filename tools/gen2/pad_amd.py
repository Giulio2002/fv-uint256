#!/usr/bin/env python3 -I
# pad_amd.py [k ...] : writes lean/Fv256/Proofs/Amd64/PaddedBytes.lean, PadDefs.lean and PadCases/Case<k>.lean (k = 0..31, 32 = Big)
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ks = [int(a) for a in sys.argv[1:]] or list(range(33))
OPEN = "\nopen Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts\n\n"
PRE = """(fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [byteType, {K}, {K}] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))"""
CTR = """(hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H)"""
def post(K, zero):
    if zero:
        return """(fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 0 ∧ (s'.regs 1).toNat = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))"""
    return f"""(fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = {K} ∧ (s'.regs 1).toNat = {K} ∧
        InRanges ptr {K} rt ∧ s'.mem.accessible ptr {K} true = true ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) {K} = valueAt s z 32 % 2 ^ (8 * {K}) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))"""
INTRO = """  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, ⟨hzw, hz⟩, hzo, hzd, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hzd ⊢
  janus64_data hd [hw]
"""
RUN = "  janus64_run [Util.readLE_32, Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.sub_self, BitVec.zero_add, BitVec.add_sub_cancel, Util.bv_add_sub_left, Util.bv_sub_sub_cancel]\n"
LIMBS = "".join(f"  have l{j} := Util.readLE8_lt s.mem {'z.toNat' if j == 0 else '(z.toNat + %d)' % (8*j)}\n" for j in range(4))
SIMP = "(try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])"
def case(k):
    big = k == 32
    nm = "caseBig" if big else f"case{k}"
    K = "n.toNat" if big else str(k)
    L = ["set_option maxRecDepth 20000 in", "set_option maxHeartbeats 64000000 in",
         f"theorem {nm} (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z{' n' if big else ''} : BitVec 64)" + (" (h32 : 32 ≤ n.toNat) (hn : n.toNat ≤ 2 ^ 48)" if big else "") + "",
         "    " + CTR + " :",
         f"    Ensures (Extracted.program.link impl) Extracted.entry [z, {'n' if big else str(k) + '#64'}]",
         "      " + PRE.replace("{K}", K), "      " + post(K, k == 0) + " := by"]
    body = INTRO
    if k == 0:
        body += "  janus64_run until [Extracted.entry + 0x2b] calls [hmk]\n  janus64_run\n  refine ⟨_, rfl, ?_⟩\n  janus_frame\n"
    else:
        body += "  janus64_run until [Extracted.entry + 0x2b] calls [hmk.pos]\n"
        body += f"  have hdj := InRanges.disjoint ‹InRanges _ _ rt› hout\n  have hdz := InRanges.disjoint ‹InRanges _ _ rt› hzo\n"
        body += RUN + LIMBS
        body += f"  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩\n  · exact (‹InRanges _ _ rt›).sub (Nat.le_refl _) (by omega)\n  · exact Janus.Arm64.Memory.accessible_mono _ ‹Janus.Arm64.Memory.accessible _ _ _ true = true› (Nat.le_refl _) (by omega)\n"
        if big:
            body += "  · simp only [valueAt, Util.readLE_32]\n    exact Util.pad_big3 _ _ n.toNat _ _ _ _ h32 ‹_› l0 l1 l2 l3\n"
        else:
            body += "  · simp only [valueAt, Util.readLE_32]\n    refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)\n    intro a ha\n"
            alts = " ∨ ".join(f"a = {j}" for j in range(k))
            body += f"    rcases (show {alts} by omega) with " + " | ".join(["rfl"] * k) + "\n"
            for j in range(k):
                e = 8*(k-1-j)
                body += "    · (try simp only [Nat.add_zero])\n      " + SIMP + "\n" + f"      first | (rw [Util.wb{e} _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb{e} _ _ _ _ l0 l1 l2 l3]; omega) | omega\n"
        body += "  · janus_frame\n"
    L.append(body.rstrip("\n"))
    return "\n".join(L)

DEFS = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\n" + OPEN + """namespace Fv256.Amd64.PaddedBytes

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (the `LEA` before the call): the extraction's only data object. -/
def byteType : Nat := dataBase Extracted.program 0

end Fv256.Amd64.PaddedBytes
"""
os.makedirs(ROOT + '/lean/Fv256/Proofs/Amd64/PadCases', exist_ok=True)
open(ROOT + '/lean/Fv256/Proofs/Amd64/PadDefs.lean', 'w').write(DEFS)
for k in ks:
    mod = "CaseBig" if k == 32 else f"Case{k}"
    open(ROOT + f'/lean/Fv256/Proofs/Amd64/PadCases/{mod}.lean', 'w').write(
        "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Amd64.PadDefs\n" + OPEN + "namespace Fv256.Amd64.PaddedBytes\n\n" + case(k) + "\n\nend Fv256.Amd64.PaddedBytes\n")

M = "import Extracted\nimport Fv256.Spec\nimport Fv256.SpecC\nimport Fv256.Util\nimport Fv256.UtilC\nimport Fv256.Amd64.PadDefs\n"
for k in range(32): M += f"import Fv256.Proofs.Amd64.PadCases.Case{k}\n"
M += "import Fv256.Proofs.Amd64.PadCases.CaseBig\n"
M += '''
/-!
# `(*uint256.Int).PaddedBytes(n int) []byte` (amd64)

Same guarantee as the arm64 theorem: for every receiver `z` (`RAX`), every `n` (`RBX`) with `n <= 2^48`, every list `rt` of runtime-owned
ranges and every implementation of `runtime.makeslice` meeting the pinned allocation contract (`MakesliceContract64`, hypothesis `hmk`), and
every Go call whose stack check falls through (stack window `[RSP-4136, RSP+24)` writable, outside `rt`), with the 32 bytes at `z`
readable, outside `rt` and the stack window: the call returns the slice `(ptr, n, n)` (`RAX`, `RBX`, `RCX`); for `n > 0`, `[ptr, ptr+n)` is
a fresh object inside `rt`, and its `n` bytes read big-endian as the number at `z` modulo `2^(8n)`; memory is unchanged outside `rt` and the
stack window. One proof module per `n = 0..31` and one for `n >= 32`.
-/
''' + OPEN + "namespace Fv256.Amd64.PaddedBytes\n\n"
M += """set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z n : BitVec 64) (hn : n.toNat ≤ 2 ^ 48)
    """ + CTR + """ :
    Ensures (Extracted.program.link impl) Extracted.entry [z, n]
      """ + PRE.replace("{K}", "n.toNat") + """
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = n.toNat ∧ (s'.regs 1).toNat = n.toNat ∧
        (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) n.toNat = valueAt s z 32 % 2 ^ (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs hpre
  by_cases h32 : 32 ≤ n.toNat
  · exact (caseBig impl rt H z n h32 hn hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
      ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
  · rcases (show """ + " ∨ ".join(f"n.toNat = {k}" for k in range(32)) + """ by omega) with """ + " | ".join(f"h{k}" for k in range(32)) + "\n"
for k in range(32):
    M += f"    · have e : n = {k}#64 := BitVec.eq_of_toNat_eq (by simpa using h{k})\n      subst e\n"
    if k == 0:
        M += "      exact (case0 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, g⟩ =>\n        ⟨hab, ptr, a, b, c, fun h => absurd h (by simp), by simp [Spec.fromBE, Nat.mod_one], g⟩\n"
    else:
        M += f"      exact (case{k} impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>\n        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩\n"
M += "\n" + open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pad_amd_witness.lean')).read() + "\nend Fv256.Amd64.PaddedBytes\n"
open(ROOT + '/lean/Fv256/Proofs/Amd64/PaddedBytes.lean', 'w').write(M)
