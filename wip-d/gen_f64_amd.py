#!/usr/bin/env python3
"""generates lean/Fv256/Amd64/Float64J{1,2,3}.lean (amd64 Float64 per-upper-limb lemmas)"""
import sys
def X(i): return "(s.mem.readLE x.toNat 8)" if i==0 else f"(s.mem.readLE (x.toNat + {8*i}) 8)"
LIT={3:"18446744073709551552",2:"18446744073709551488",1:"18446744073709551424"}
def lemma(j):
    c=64*j+64
    zs=list(range(j+1,4))          # limbs that are zero
    pre_extra=" ∧ ".join([f"{X(i)} = 0" for i in zs]+[f"{X(j)} ≠ 0"])
    names=", ".join([f"hz{i}" for i in zs]+["hxj"])
    zf="".join(f", hz{i}" for i in zs)
    zsimp=("Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff"+zf+", hxj")
    blargs=' '.join(X(i) for i in range(j+1)); lim=' '.join(f"l{i}" for i in range(j+1))
    UP="Fv256.D.Up (s'.mem.readLE (BitVec.toNat (s.regs 4) - 40) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 32) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 24) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 16) 8)"
    S="simp only [Fv256.D.Up, Fv256.D.lsb32 _ 11 (by decide), Fv256.D.lsb32 _ 12 (by decide), Fv256.D.ite_tf, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at *; omega"
    HBL = 'have h := hbl; simp only [Nat.mul_zero, Nat.add_zero] at h; exact h' if zs else 'simpa using hbl'
    LIMB=["s.mem.readLE x.toNat 8","18446744073709551616 * s.mem.readLE (x.toNat + 8) 8","340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8","6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8"]
    COEF=[None,"18446744073709551616","340282366920938463463374607431768211456","6277101735386680763835789423207666416102355444464034512896"]
    parts=[LIMB[i] for i in range(j+1)]
    V="("+" + ".join(parts)+")"
    off=64*j+1
    E=f"(BitVec.ofNat 64 (63 - k + {off}))"
    HAVES=f"""  all_goals have a1 : {E}.toNat = {c} - k := (by simp only [BitVec.toNat_ofNat]; omega)
  all_goals have a2 : Spec.bitLen {V} = {c} - k := (by {HBL})
  all_goals have a3 : {V} < 2 ^ 256 := (by omega)
  all_goals have a4 : 2 ^ 64 ≤ {V} := (by omega)
  all_goals have a5 : (s'.mem.readLE (BitVec.toNat (s.regs 4) - 40) 8) + 2 ^ 64 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 32) 8) + 2 ^ 128 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 24) 8) + 2 ^ 192 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 16) 8) = {V} * 2 ^ (257 - ({c} - k)) % 2 ^ 256 := (by rw [show 257 - ({c} - k) = {257-c} + k by omega]; exact hS4)
"""
    def leaf(L,neg):
        hv="\n".join("       "+l.replace("  all_goals ","",1) for l in HAVES.rstrip("\n").split("\n"))
        return f"""    | (have hu : {neg}{UP} := by {S}
{hv}
       exact Fv256.D.{L} {V} ({c} - k) _ _ _ _ {E} a1 a3 a4 a2 m0 m1 m2 m3 a5 hu)"""
    hc = "" if j==3 else ""
    return f"""import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.CodeIn
import Fv256.LshProg
import Fv256.Amd64.LshSum
import Fv256.Amd64.Float64Hc

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

namespace Fv256.Amd64.Float64

set_option maxHeartbeats 4000000 in
theorem lem{j} (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => (StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s) ∧
        {pre_extra})
      (fun s s' => (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64BitsNearest (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 80, (s.regs regSP).toNat + 8)]) := by
  intro ret hret s hs ⟨⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hxw, hx⟩, hds, hm⟩, {"⟨"+names+"⟩" if len(zs)>0 else "hxj"}⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, {zsimp}] calls [hS := Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshSum.lsh_summary (s.regs 4 - 40#64) x)]
  all_goals clear_states
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  all_goals clear hS
  all_goals grab_lsh hS3
  all_goals (simp (disch := omega) only [valueAt, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside] at hS3)
  all_goals have l0 := Util.readLE8_lt s.mem x.toNat
  all_goals have l1 := Util.readLE8_lt s.mem (x.toNat + 8)
  all_goals have l2 := Util.readLE8_lt s.mem (x.toNat + 16)
  all_goals have l3 := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals have hkj : Janus.Arm64.clzNat 64 {X(j)} < 64 := (Fv256.B.clz_cases _ l{j}).resolve_left hxj
  all_goals have hbl := Fv256.B.f64_bl{j} {blargs} (Janus.Arm64.clzNat 64 {X(j)}) {lim} hxj rfl
  all_goals generalize Janus.Arm64.clzNat 64 {X(j)} = k at *
  all_goals have m0 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 40)
  all_goals have m1 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 32)
  all_goals have m2 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 24)
  all_goals have m3 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 16)
  all_goals have hsp40 : BitVec.toNat (s.regs 4 - 40#64) = BitVec.toNat (s.regs 4) - 40 := (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  all_goals have hexp : (18446744073709551616 - ({LIT[j]} + (63 - k))) = {257-c} + k := by omega
  all_goals have e8 : BitVec.toNat (s.regs 4) - 40 + 8 = BitVec.toNat (s.regs 4) - 32 := by omega
  all_goals have e16 : BitVec.toNat (s.regs 4) - 40 + 16 = BitVec.toNat (s.regs 4) - 24 := by omega
  all_goals have e24 : BitVec.toNat (s.regs 4) - 40 + 24 = BitVec.toNat (s.regs 4) - 16 := by omega
  all_goals have hS4 := hS3
  all_goals simp only [hexp, hsp40, e8, e16, e24{zf}{', Nat.mul_zero, Nat.add_zero' if zs else ''}] at hS4
  all_goals first
{leaf("leafA0","¬ ")}
{leaf("leafA1","")}

end Fv256.Amd64.Float64
"""
for j in (1,2,3):
    open(f'/srv/fv-uint256-wd/lean/Fv256/Amd64/Float64J{j}.lean','w').write(lemma(j))
open('/srv/fv-uint256-wd/lean/Fv256/Amd64/Float64Hc.lean','w').write("""import Extracted
import Fv256.CodeIn
import Fv256.LshProg

namespace Fv256.Amd64.Float64

set_option maxRecDepth 100000 in
theorem hcLsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.LshProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

end Fv256.Amd64.Float64
""")
