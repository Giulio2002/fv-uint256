import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SumC64
import Fv256.Amd64.SfdEnv
import Fv256.Amd64.SfdTePre

/-!
# The interface of the `toError` summary in terms of `Env`

`TePre'` states the precondition of `strconv.toError` (`SfdToError.TePre`) with the window-based facts packaged as
`SfdEnv.Env` (for the window `[RSP - 4192, RSP + 72)`), the model facts `Mod` and the per-call `ChunkOK`;
`tePre_of_pre'` derives `TePre`.  Callers establish `TePre'` from their own `Env` (`Env.shrink`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError

namespace Fv256.Amd64.SfdBridge

/-- the state-independent model facts -/
def Mod (R : RtInv) (R2 : IfaceModel) (T : Nat) (L : List (Nat × Nat)) : Prop :=
  R2.Laws ∧ R2.depth ≤ 4096 ∧ R2.IsType T ∧ (∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv) ∧ (∀ r ∈ R.rt, 0 < r.1) ∧
  (∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) R.rt) ∧ (∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) R2.priv) ∧
  R.ok (Extracted.program.contractAddr "runtime.newobject") [numErrType] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2]

/-- the facts about the string `(sp, sl)` being copied -/
def ChunkOK (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (b : Nat) (sp sl : BitVec 64) (lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  R.ok (Extracted.program.contractAddr "runtime.mallocgc") [sl.toNat, 0, 0] ∧
  (∀ q, R.ok (Extracted.program.contractAddr "runtime.memmove") [q, sp.toNat, sl.toNat]) ∧
  blockSize sl.toNat true + blockSize 48 false ≤ b ∧
  m.accessible sp.toNat sl.toNat false = true ∧ sp.toNat + sl.toNat ≤ 2 ^ 48 ∧
  (sp.toNat + sl.toNat ≤ lo ∨ hi ≤ sp.toNat) ∧
  (Outside sp.toNat sl.toNat R.rt ∨ InRanges sp.toNat sl.toNat L) ∧ Outside sp.toNat sl.toNat R2.priv


open Fv256.C in
def TePre' (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = fp ∧ s.regs 3 = fl ∧ s.regs 1 = sp ∧ s.regs 7 = sl ∧
  s.regs 9 = BitVec.ofNat 64 errItab ∧ s.regs 10 = BitVec.ofNat 64 synConst ∧ 1 ≤ sl.toNat ∧ sl.toNat < 2 ^ 40 ∧
  4192 ≤ (s.regs 4).toNat ∧ Mod R R2 T L ∧
  Env R R2 T b L ((s.regs 4).toNat - 4192) ((s.regs 4).toNat + 72) s ∧
  ChunkOK R R2 L b sp sl ((s.regs 4).toNat - 4192) ((s.regs 4).toNat + 72) s.mem

theorem tePre_of_pre' {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64}
    {s : State} (h : TePre' R R2 T b L fp fl sp sl s) : TePre R R2 T b L fp fl sp sl s := by
  obtain ⟨hret, h0, h3, h1, h7, h9, h10, hsl1, hsl2, hlow, ⟨hl, hdep, hty, hpr, hLp, hrt0, hsR, hsP, hokn, hok1, hok2⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩,
    ⟨hokm, hokv, hbud, hsacc, hsp48, hsdisj, hspR, hspP⟩⟩ := h
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := e15
  have oI := e14 (errItab, errItab + 16) (by simp [staticRanges])
  have oS := e14 (synConst, synConst + 8) (by simp [staticRanges])
  have oE := e14 (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
  have oW := e14 (wbFlag, wbFlag + 4) (by simp [staticRanges])
  have oN := e14 (numErrType, numErrType + 16) (by simp [staticRanges])
  have pN := hsR (numErrType, numErrType + 16) (by simp [staticRanges])
  have pW := hsR (wbFlag, wbFlag + 4) (by simp [staticRanges])
  have pE := hsR (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
  have qN := hsP (numErrType, numErrType + 16) (by simp [staticRanges])
  have qW := hsP (wbFlag, wbFlag + 4) (by simp [staticRanges])
  have qE := hsP (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
  simp only [Nat.add_sub_cancel_left] at oI oS oE oW oN pN pW pE qN qW qE
  have hw : (s.regs 4).toNat + 72 - ((s.regs 4).toNat - 4192) = 4264 := by omega
  rw [hw] at e9 e10
  refine ⟨hret, h0, h3, h1, h7, h9, h10, hsl1, hsl2, ?_, ?_, e4, t6, t7, t12, t10, t11, hdep, ?_, e9, e17, e18, hbud, t1, hty, t3, t4, t5,
    oI, oS, oE, oW, oN, hpr, hLp, pN, pW, pE, hokm, hokn, hokv, hok1, hok2, ?_, hsp48, hsdisj, ?_, e11, hrt0, qN, qW, qE, t8, t9, hspR, hspP⟩
  · exact ⟨by simp only [regG, stackguard0Offset]; omega, by simp only [regG, stackguard0Offset]; exact e7, by
      simp only [stackguard0, regG, regSP, stackguard0Offset]; omega⟩
  · exact ⟨hlow, by omega, by
      have := e5
      rw [hw] at this
      simpa using this⟩
  · refine ⟨e16, ⟨by simp only [regG, stackguard0Offset]; omega, by simp only [regG, stackguard0Offset]; exact e7, by
      simp only [stackguard0, regG, regSP, stackguard0Offset]; omega⟩, e4, by omega, by omega, ?_, ?_, ?_, e12⟩
    · have := e5
      rw [hw] at this
      exact Arm64.Memory.accessible_mono _ this (by omega) (by omega)
    · exact Outside.of_sub e10 (by omega) (by omega)
    · simp only [Spec.Disjoint]; omega
  · simpa using hsacc
  · simp only [Spec.Disjoint]; omega

end Fv256.Amd64.SfdBridge
