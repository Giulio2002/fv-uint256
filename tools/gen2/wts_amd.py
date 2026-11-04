#!/usr/bin/env python3 -I
# wts_amd.py [k ...] : writes lean/Fv256/Amd64/WriteToSlice.lean and lean/Fv256/Amd64/WtsCases/Case<k>.lean
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ks = [int(a) for a in sys.argv[1:]] or list(range(33))
PRE = """(fun s => StackWritable s 8 24 ∧ Buffer s z 32 false ∧ Buffer s d {K} true ∧
        (z.toNat + 32 ≤ d.toNat ∨ d.toNat + {K} ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (d.toNat + {K} ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ d.toNat) ∧ {CK} ≤ cap.toNat)"""
POST = """(fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) {N} = valueAt s z 32 % 2 ^ (8 * {N}) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat {N} ((s.regs regSP).toNat - 8) 32)"""
def cname(k): return f"case{k}" if k < 32 else "caseBig"
def mname(k): return f"Case{k}" if k < 32 else "CaseBig"
RUN = "janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod{X}]"
def lemma(k):
    n = min(k, 32); big = k >= 32
    lenarg = "len" if big else f"{k}#64"
    K = "32" if big else str(k)
    L = ["set_option maxHeartbeats 64000000 in",
         f"theorem {cname(k)} (z d {'len ' if big else ''}cap : BitVec 64)" + (" (h32 : 32 ≤ len.toNat) (hlen : len.toNat < 2 ^ 48)" if big else "") + " :",
         f"    Ensures Extracted.program Extracted.entry [z, d, {lenarg}, cap]",
         "      " + PRE.replace("{K}", K).replace("{CK}", "len.toNat" if big else str(k)),
         "      " + POST.replace("{N}", str(n)) + " := by",
         "  intro ret hret s hs ⟨⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hdw, hd⟩, hzd, hzs, hds, hcap⟩",
         "  janus64_intro hs",
         "  simp only [regSP] at hacc hlow hnw hzs hds",
         "  simp only [valueAt, Disjoint]"]
    if big:
        L.append("  " + RUN.replace("{X}", ""))
    else:
        L.append("  " + RUN.replace("{X}", ""))
    L += ["  have l0 := Util.readLE8_lt s.mem z.toNat", "  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)",
          "  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)", "  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)",
          "  refine ⟨?_, ?_⟩"]
    if n == 0:
        L.append("  · simp [Spec.fromBE, Nat.mod_one]")
    else:
        L += ["  · refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)", "    intro a ha"]
        alts = " ∨ ".join(f"a = {j}" for j in range(n))
        L.append(f"    rcases (show {alts} by omega) with " + " | ".join(["rfl"] * n))
        for j in range(n):
            L += ["    · (try simp only [Nat.add_zero])",
                  "      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]",
                  f"      first | (rw [Util.wb{8*(n-1-j)} _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb{8*(n-1-j)} _ _ _ _ l0 l1 l2 l3]; omega) | omega"]
    L.append("  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]")
    return "\n".join(L)
HDR = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\n"
OPEN = "\nopen Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\n\n"
os.makedirs(ROOT + '/lean/Fv256/Amd64/WtsCases', exist_ok=True)
for k in ks:
    open(ROOT + f'/lean/Fv256/Amd64/WtsCases/{mname(k)}.lean', 'w').write(
        HDR + OPEN + "namespace Fv256.Amd64.WriteToSlice\n\n" + lemma(k) + "\n\nend Fv256.Amd64.WriteToSlice\n")
if len(ks) == 33:
    imports = "".join(f"import Fv256.Amd64.WtsCases.{mname(k)}\n" for k in ks)
    main = HDR + imports + OPEN + "namespace Fv256.Amd64.WriteToSlice\n" + """
/-!
# `(*uint256.Int).WriteToSlice(dest []byte)` (amd64)

**Guarantee.** For every pointer `z` (the receiver, `RAX`) and slice `dest = (d, len, cap)` (`RBX`, `RCX`, `RDI`) and every Go call
state such that the return-address slot and the frame window `[RSP-8, RSP+24)` are writable: if the 32 bytes at `z` are readable, the
`len` bytes at `d` writable, `len < 2^48`, and neither `z` nor `dest` overlaps the other or that window, then the call returns (no
fault, no panic), obeys the ABI, with `n = min len 32` the first `n` bytes of `dest` read as the big-endian number
`Fv256.Spec.fromBE` equal to the low `8n` bits of the number at `z` (`dest[n-1-j]` is byte `j` of `z`), and no byte changes outside
`dest[0..n)` and the frame window (`Fv256.Util.OnlyWrites2`). (`len = 0` writes nothing; bytes of `dest` beyond index 31 are not touched.)

**How.** The byte loop has a constant trip count for each `n`: the proof splits on `len` (33 cases, one module each under
`Fv256.Amd64.WtsCases`), and `janus64_run` unrolls the loop.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

set_option maxHeartbeats 64000000 in
theorem correctness (z d len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, len, cap]
      (fun s => StackWritable s 8 24 ∧ Buffer s z 32 false ∧ len.toNat < 2 ^ 48 ∧ Buffer s d len.toNat true ∧
        (z.toNat + 32 ≤ d.toNat ∨ d.toNat + len.toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (d.toNat + len.toNat ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ d.toNat) ∧
        len.toNat ≤ cap.toNat)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min len.toNat 32) =
          valueAt s z 32 % 2 ^ (8 * min len.toNat 32) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) ((s.regs regSP).toNat - 8) 32) := by
  intro ret hret s hs ⟨hst, hz, hl, hd, hzd, hzs, hds, hcap⟩
  by_cases h32 : 32 ≤ len.toNat
  · have := caseBig z d len cap h32 hl ret hret s hs ⟨hst, hz, ⟨by have := hd.1; omega, Janus.Arm64.Memory.accessible_mono _ hd.2 (Nat.le_refl _) (by omega)⟩, by omega, by omega, by omega, hcap⟩
    simpa [Nat.min_eq_right h32] using this
  · have e : len = BitVec.ofNat 64 len.toNat := by simp
    rcases (show """ + " ∨ ".join(f"len.toNat = {k}" for k in range(32)) + """ by omega) with """ + " | ".join(f"h{k}" for k in range(32)) + "\n"
    for k in range(32):
        main += f"""    · have e{k} : len = {k}#64 := by rw [e, h{k}]
      subst e{k}
      have := case{k} z d cap ret hret s hs ⟨hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
"""
    main += """
namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def d : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then d else if i = 1 then 8 else if i = 7 then 8
      else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 8 24 ∧ Buffer s0 z 32 false ∧ (8 : BitVec 64).toNat < 2 ^ 48 ∧
    Buffer s0 d (8 : BitVec 64).toNat true ∧
    (z.toNat + 32 ≤ d.toNat ∨ d.toNat + (8 : BitVec 64).toNat ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (d.toNat + (8 : BitVec 64).toNat ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24 ≤ d.toNat) ∧
    (8 : BitVec 64).toNat ≤ (8 : BitVec 64).toNat :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide⟩

theorem nonvacuous : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s0 ∧
    (StackWritable s0 8 24 ∧ Buffer s0 z 32 false ∧ (8 : BitVec 64).toNat < 2 ^ 48 ∧
    Buffer s0 d (8 : BitVec 64).toNat true ∧
    (z.toNat + 32 ≤ d.toNat ∨ d.toNat + (8 : BitVec 64).toNat ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (d.toNat + (8 : BitVec 64).toNat ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24 ≤ d.toNat) ∧
    (8 : BitVec 64).toNat ≤ (8 : BitVec 64).toNat) :=
  ⟨setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧
    Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min (8 : BitVec 64).toNat 32) =
      valueAt s0 z 32 % 2 ^ (8 * min (8 : BitVec 64).toNat 32) ∧
    Util.OnlyWrites2 s0.mem s'.mem d.toNat (min (8 : BitVec 64).toNat 32) ((s0.regs regSP).toNat - 8) 32) :=
  correctness z d 8 8 ret hret s0 setup hpre

end Witness

end Fv256.Amd64.WriteToSlice
"""
    open(ROOT + '/lean/Fv256/Amd64/WriteToSlice.lean', 'w').write(main)
