#!/usr/bin/env python3 -I
# pad_arm.py [k ...] : writes lean/Fv256/Proofs/Arm64/PaddedBytes.lean, PadDefs.lean and PadCases/Case<k>.lean (k = 0..31, 32 = Big)
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ks = [int(a) for a in sys.argv[1:]] or list(range(33))
OPEN = "\nopen Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts\n\n"
PRE = """(fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, {K}, {K}] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))"""
CTR = """(hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H)"""
def post(K, zero):
    if zero:
        return f"""(fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = 0 ∧ (s'.regs 2).toNat = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))"""
    return f"""(fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = {K} ∧ (s'.regs 2).toNat = {K} ∧
        InRanges ptr {K} rt ∧ s'.mem.accessible ptr {K} true = true ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) {K} = val256 s.mem z.toNat % 2 ^ (8 * {K}) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))"""
INTRO = "  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩\n  janus_intro hs\n  janus_eval_nat h_pt : byteType\n  rw [h_pt] at hH\n  janus_data hd [hw]\n  simp only [Disjoint] at hzd\n"
RUN = "  janus_run [Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.sub_self, BitVec.zero_add, BitVec.add_sub_cancel, Util.bv_add_sub_left]\n"
LIMBS = "".join(f"  have l{j} := Util.readLE8_lt s.mem {'z.toNat' if j == 0 else '(z.toNat + %d)' % (8*j)}\n" for j in range(4))
def case(k):
    big = k == 32
    nm = "caseBig" if big else f"case{k}"
    K = "n.toNat" if big else str(k)
    L = ["set_option maxRecDepth 20000 in", "set_option maxHeartbeats 64000000 in",
         f"theorem {nm} (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z{' n' if big else ''} : BitVec 64)" + (" (h32 : 32 ≤ n.toNat) (hn : n.toNat ≤ 2 ^ 48)" if big else ""),
         "    " + CTR + " :",
         f"    Ensures (Extracted.program.link impl) Extracted.entry [z, {'n' if big else str(k) + '#64'}]",
         "      " + PRE.replace("{K}", K), "      " + post(K, k == 0) + " := by"]
    body = INTRO
    if k == 0:
        body += "  janus_run until [Extracted.entry + 0x30] calls [hmk]\n  janus_run\n  refine ⟨_, rfl, ?_⟩\n  janus_frame\n".replace("\\n", "\n")
    else:
        body += "  janus_run until [Extracted.entry + 0x30] calls [hmk.pos]\n  rename_i wobj wregs wflags wvreg wmem wo wx hmf hin hle hacc h8 h16 hzb htr\n  have hdj := InRanges.disjoint hin hout\n  have hdz := InRanges.disjoint hin hzo\n"
        body += RUN + LIMBS
        if big:
            body += "  have hbs : n.toNat ≤ blockSize n.toNat true := by\n    unfold blockSize; split\n    · exact Nat.le_refl _\n    · exact le_roundupsize _ _\n"
        body += "  refine ⟨_, rfl, hin.sub (Nat.le_refl _) (by omega), Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), ?_, ?_⟩\n"
        if big:
            body += "  · exact Util.pad_big2 wmem _ n.toNat _ _ _ _ h32 hzb l0 l1 l2 l3\n"
        else:
            body += "  · refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)\n    intro a ha\n"
            alts = " ∨ ".join(f"a = {j}" for j in range(k))
            body += f"    rcases (show {alts} by omega) with " + " | ".join(["rfl"] * k) + "\n"
            for j in range(k):
                e = 8*(k-1-j)
                body += "    · (try simp only [Nat.add_zero])\n      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])\n" + f"      first | (rw [Util.wb{e} _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb{e} _ _ _ _ l0 l1 l2 l3]; omega) | omega\n"
        body += "  · janus_frame\n"
    L.append(body.rstrip("\n"))
    return "\n".join(L)

DEFS = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\n" + OPEN + """namespace Fv256.Arm64.PaddedBytes

/-- the type descriptor of `uint8` passed to `runtime.makeslice` (ADRP + ADD at entry+0x20). -/
def byteType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.(*Int).PaddedBytes" 8)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).PaddedBytes" 9) 0

end Fv256.Arm64.PaddedBytes
"""
os.makedirs(ROOT + '/lean/Fv256/Proofs/Arm64/PadCases', exist_ok=True)
open(ROOT + '/lean/Fv256/Proofs/Arm64/PadDefs.lean', 'w').write(DEFS)
for k in ks:
    mod = "CaseBig" if k == 32 else f"Case{k}"
    open(ROOT + f'/lean/Fv256/Proofs/Arm64/PadCases/{mod}.lean', 'w').write(
        "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Arm64.PadDefs\n" + OPEN + "namespace Fv256.Arm64.PaddedBytes\n\n" + case(k) + "\n\nend Fv256.Arm64.PaddedBytes\n")

# ---- main file
M = "import Extracted\nimport Fv256.Spec\nimport Fv256.SpecC\nimport Fv256.Util\nimport Fv256.UtilC\nimport Fv256.Arm64.PadDefs\n"
for k in range(32): M += f"import Fv256.Proofs.Arm64.PadCases.Case{k}\n"
M += "import Fv256.Proofs.Arm64.PadCases.CaseBig\n"
M += '''
/-!
# `(*uint256.Int).PaddedBytes(n int) []byte` (arm64)

**Guarantee.** For every receiver `z` (`X0`), every `n` (`X1`) with `n <= 2^48` (the `runtime.makeslice` panic paths, negative or oversized
`n`, are excluded), every list `rt` of runtime-owned ranges and **every** implementation of `runtime.makeslice` meeting the pinned
allocation contract (`MakesliceContract`, hypothesis `hmk`), and every Go call whose stack check falls through (stack window
`[SP-4144, SP+24)` writable, aligned, outside `rt`), with the 32 bytes at `z` readable, outside `rt` and the stack window: the call
returns the slice `(ptr, n, n)`; for `n > 0`, `[ptr, ptr+n)` is a fresh object inside `rt` (writable), and its `n` bytes read big-endian
(`Fv256.Spec.fromBE`) as the number at `z` modulo `2^(8n)` (so zero padding on the left for `n > 32`, truncation of the high bytes for `n < 32`);
memory is unchanged outside `rt` and the stack window. The loop is unrolled: one proof module per `n = 0..31` and one for `n >= 32`.

**What is assumed.** Only the contract hypothesis `hmk` for the code linked at `runtime.makeslice` (not extracted).

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`: a toy allocator at the `makeslice` address; for `n = 5` the call returns a slice of length and capacity 5.
-/
''' + OPEN + "namespace Fv256.Arm64.PaddedBytes\n\n"
M += """set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z n : BitVec 64) (hn : n.toNat ≤ 2 ^ 48)
    """ + CTR + """ :
    Ensures (Extracted.program.link impl) Extracted.entry [z, n]
      """ + PRE.replace("{K}", "n.toNat") + """
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = n.toNat ∧ (s'.regs 2).toNat = n.toNat ∧
        (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) n.toNat = val256 s.mem z.toNat % 2 ^ (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
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
M += "\n" + open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pad_arm_witness.lean')).read()
open(ROOT + '/lean/Fv256/Proofs/Arm64/PaddedBytes.lean', 'w').write(M)
