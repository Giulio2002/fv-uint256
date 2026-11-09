#!/usr/bin/env python3 -I
# wts_arm.py [k ...] : writes lean/Fv256/Proofs/Arm64/WriteToSlice.lean and lean/Fv256/Proofs/Arm64/WtsCases/Case<k>.lean
# (the byte loop is unrolled: one module per min(len,32), so each module stays small)
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ks = [int(a) for a in sys.argv[1:]] or list(range(33))
PRE = """(fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧
        Ptr s.mem d {K} true ∧ Disjoint z.toNat 32 d.toNat {K} ∧
        Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat {K} (s.sp.toNat - 24) 48 ∧ {K} ≤ cap.toNat)"""
POST = """(fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) {N} = val256 s.mem z.toNat % 2 ^ (8 * {N}) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat {N} (s.sp.toNat - 24) 48)"""
def cname(k): return f"case{k}" if k < 32 else "caseBig"
def mname(k): return f"Case{k}" if k < 32 else "CaseBig"
def lemma(k):
    n = min(k, 32)
    big = k >= 32
    lenarg = "len" if big else f"{k}#64"
    K = "len.toNat" if big else str(k)
    L = []
    L.append("set_option maxHeartbeats 64000000 in")
    L.append(f"theorem {cname(k)} (z d {'len ' if big else ''}cap : BitVec 64)" + (" (h32 : 32 ≤ len.toNat) (hlen : len.toNat < 2 ^ 48)" if big else "") + " :")
    L.append(f"    Ensures Extracted.program Extracted.entry [z, d, {lenarg}, cap]")
    L.append("      " + PRE.replace("{K}", K))
    L.append("      " + POST.replace("{N}", str(n)) + " := by")
    L.append("  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hd, hd'⟩, hzd, hzs, hds, hcap⟩")
    L.append("  janus_intro hs")
    L.append("  simp only [Disjoint] at *")
    if big:
        L.append("  have e1 : (len - 1#64).toNat = len.toNat - 1 := by")
        L.append("    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; have := len.isLt; omega")
        L.append("  have hmin : (if 31 < ((len.toNat - 1 : Nat) : Int) then 31#64 else len - 1#64) = 31#64 := by")
        L.append("    split")
        L.append("    · rfl")
        L.append("    · apply BitVec.eq_of_toNat_eq")
        L.append("      rw [e1]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega")
        L.append("  janus_run [Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hmin]")
    else:
        L.append("  janus_run [Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]")
    L.append("  have l0 := Util.readLE8_lt s.mem z.toNat")
    L.append("  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)")
    L.append("  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)")
    L.append("  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)")
    L.append("  refine ⟨?_, ?_⟩")
    if n == 0:
        L.append("  · simp [Spec.fromBE, Nat.mod_one]")
    else:
        L.append("  · refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)")
        L.append("    intro a ha")
        alts = " ∨ ".join(f"a = {j}" for j in range(n))
        L.append(f"    rcases (show {alts} by omega) with " + " | ".join(["rfl"] * n))
        for j in range(n):
            L.append("    · (try simp only [Nat.add_zero])")
            L.append("      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])")
            L.append(f"      first | (rw [Util.wb{8*(n-1-j)} _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb{8*(n-1-j)} _ _ _ _ l0 l1 l2 l3]; omega) | omega")
    L.append("  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]")
    return "\n".join(L)
HDR = """import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
"""
OPEN = """
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

"""
os.makedirs(ROOT + '/lean/Fv256/Proofs/Arm64/WtsCases', exist_ok=True)
for k in ks:
    open(ROOT + f'/lean/Fv256/Proofs/Arm64/WtsCases/{mname(k)}.lean', 'w').write(
        HDR + OPEN + "namespace Fv256.Arm64.WriteToSlice\n\n" + lemma(k) + "\n\nend Fv256.Arm64.WriteToSlice\n")
if len(ks) == 33:
    imports = "".join(f"import Fv256.Proofs.Arm64.WtsCases.{mname(k)}\n" for k in ks)
    main = HDR + imports + OPEN + "namespace Fv256.Arm64.WriteToSlice\n" + """
/-!
# `(*uint256.Int).WriteToSlice(dest []byte)` (arm64)

**Guarantee.** For every pointer `z` (the receiver, `X0`) and slice `dest = (d, len, cap)` (`X1`-`X3`), every Go call whose
stack-growth check falls through (`GuardOK s 0`) and whose stack window `[SP-24, SP+24)` is writable and aligned
(`StackOK s 24 24`): if the 32 bytes at `z` are readable, the `len` bytes at `d` writable, `len < 2^48`, `len ≤ cap` (a valid slice), and neither `z` nor `dest`
overlaps the other or the stack window, then the call returns (no fault, no panic), obeys the ABI, with `n = min len 32` the first `n`
bytes of `dest` read as the big-endian number `Fv256.Spec.fromBE` equal to the low `8n` bits of the number at `z` (the last
`n` bytes are written, i.e. `dest[n-1-j]` is byte `j` of `z`), and no byte changes outside `dest[0..n)` and the stack window
(`Fv256.Util.OnlyWrites2`). (`len = 0` writes nothing; bytes of `dest` beyond index 31 are not touched.)

**How.** The byte loop has a constant trip count for each `n`: the proof splits on `len` (33 cases, one module each under
`Fv256.Arm64.WtsCases`), and `janus_run` unrolls the loop.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

set_option maxHeartbeats 64000000 in
theorem correctness (z d len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧ len.toNat < 2 ^ 48 ∧
        Ptr s.mem d len.toNat true ∧ Disjoint z.toNat 32 d.toNat len.toNat ∧
        Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat len.toNat (s.sp.toNat - 24) 48 ∧
        len.toNat ≤ cap.toNat)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min len.toNat 32) =
          val256 s.mem z.toNat % 2 ^ (8 * min len.toNat 32) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) (s.sp.toNat - 24) 48) := by
  intro ret hret s hs ⟨hg, hst, hz, hl, hd, hzd, hzs, hds, hcap⟩
  by_cases h32 : 32 ≤ len.toNat
  · have := caseBig z d len cap h32 hl ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, hcap⟩
    simpa [Nat.min_eq_right h32] using this
  · have e : len = BitVec.ofNat 64 len.toNat := by simp
    rcases (show """ + " ∨ ".join(f"len.toNat = {k}" for k in range(32)) + """ by omega) with """ + " | ".join(f"h{k}" for k in range(32)) + "\n"
    for k in range(32):
        main += f"""    · have e{k} : len = {k}#64 := by rw [e, h{k}]
      subst e{k}
      have := case{k} z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
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
  { regs := fun i => if i = 0 then z else if i = 1 then d else if i = 2 then 8 else if i = 3 then 8
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 24 24 ∧ Ptr32 s0.mem z false ∧ (8 : BitVec 64).toNat < 2 ^ 48 ∧
    Ptr s0.mem d (8 : BitVec 64).toNat true ∧ Disjoint z.toNat 32 d.toNat (8 : BitVec 64).toNat ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 24) 48 ∧ Disjoint d.toNat (8 : BitVec 64).toNat (s0.sp.toNat - 24) 48 ∧
    (8 : BitVec 64).toNat ≤ (8 : BitVec 64).toNat := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, by decide,
    ⟨by decide, by decide⟩, ?_, ?_, ?_, by decide⟩ <;> (try unfold Disjoint) <;> decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s ∧
    (GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧ (8 : BitVec 64).toNat < 2 ^ 48 ∧
    Ptr s.mem d (8 : BitVec 64).toNat true ∧ Disjoint z.toNat 32 d.toNat (8 : BitVec 64).toNat ∧
    Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat (8 : BitVec 64).toNat (s.sp.toNat - 24) 48 ∧
    (8 : BitVec 64).toNat ≤ (8 : BitVec 64).toNat) :=
  ⟨ret, s0, z, d, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧
    Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min (8 : BitVec 64).toNat 32) =
      val256 s0.mem z.toNat % 2 ^ (8 * min (8 : BitVec 64).toNat 32) ∧
    Util.OnlyWrites2 s0.mem s'.mem d.toNat (min (8 : BitVec 64).toNat 32) (s0.sp.toNat - 24) 48) :=
  correctness z d 8 8 ret hret s0 setup hpre

end Witness

end Fv256.Arm64.WriteToSlice
"""
    open(ROOT + '/lean/Fv256/Proofs/Arm64/WriteToSlice.lean', 'w').write(main)
