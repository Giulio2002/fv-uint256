import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Amd64.SfdTopSpec
import Fv256.Proofs.Amd64.SfdEnvC
import Fv256.Proofs.Amd64.FromDecimalSpec
import Fv256.Spec.Amd64.UnmarshalSpec

/-!
# `UnmarshalText` / `UnmarshalJSON` (amd64): precondition and the `SetFromDecimal` call-site lemma (Extracted-free)

`string(input)` is `runtime.slicebytetostring(buf, ptr, n)` (a live runtime contract).  `PreU` is the entry precondition
(the model facts of `SfdTopSpec.TopPre` for the receiver `z`, the input slice, the contract's own model facts);
`toppre_dec` builds `TopPre` for the `SetFromDecimal` call from the state after the copy.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.UnmarshalSpec

variable (C : SfdCfg)

/-! `Mod` accessors: the only place that destructures `Mod` (so a change of `Mod` is a one-place edit). -/
theorem Mod.laws {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) : R2.Laws := by
  obtain ⟨m1, -⟩ := h; exact m1

theorem Mod.priv {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) :
    ∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt := by
  obtain ⟨m1, m2, m3, m4, -⟩ := h; exact m4

theorem Mod.lpriv {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) :
    ∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv := by
  obtain ⟨m1, m2, m3, m4, m5, -⟩ := h; exact m5

theorem Mod.static {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) :
    ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) R.rt := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, -⟩ := h; exact m7

theorem Mod.extL {R : RtInv} {R2 : IfaceModel} {T : Nat} {L L' : List (Nat × Nat)} (h : Mod C R R2 T L)
    (h' : ∀ r ∈ L', Outside r.1 (r.2 - r.1) R2.priv) : Mod C R R2 T L' := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := h
  exact ⟨m1, m2, m3, m4, h', m6, m7, m8, m9, m10, m11⟩

/-- entry precondition of `UnmarshalText`/`UnmarshalJSON`: receiver `z` in `RAX`, input slice `(pI, nI)` in `RBX`/`RCX`.
`[lo, hi)` is the absolute stack window.  `sb` is the address of `runtime.slicebytetostring`, `st` that of `runtime.staticuint64s`. -/
structure PreUS (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop where
  ret : RetOK s
  r0 : s.regs 0 = z
  r3 : s.regs 3 = pI
  r1 : s.regs 1 = nI
  mod : Mod C R R2 T L
  env : Env C R R2 T b L lo hi s
  lo4 : lo + 4904 ≤ (s.regs 4).toNat
  hi4 : (s.regs 4).toNat + 24 ≤ hi
  okH : R.ok sb [(s.regs 4).toNat - 72, pI.toNat, nI.toNat]
  okD : R.ok sb [(s.regs 4).toNat - 40, pI.toNat, nI.toNat]
  cost : roundupsize nI.toNat true ≤ b
  stWin : Outside st 2048 [(lo, hi)]
  stRt : Outside st 2048 R.rt
  stPriv : Outside st 2048 R2.priv
  stZ : Outside st 2048 [(z.toNat, z.toNat + 32)]
  mult : MultOK C z.toNat lo hi s.mem
  multRt : Outside C.mulTab 40 R.rt
  multK : ∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt
  eofA : s.mem.accessible C.ioEOF 16 false = true
  eofW : Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]
  eofR : Outside C.ioEOF 16 R.rt
  bigA : s.mem.accessible C.errBig 16 false = true
  bigW : Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]
  bigR : Outside C.errBig 16 R.rt
  init : Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem
  maxA : s.mem.accessible C.maxStr 78 false = true
  maxW : Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]
  maxR : Outside C.maxStr 78 R.rt
  maxB : ∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k
  zbuf : Buffer s z 32 true
  zwin : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat
  zR : Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L
  zP : Outside z.toNat 32 R2.priv
  zS : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]
  zg : (s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16
  ibuf : Buffer s pI nI.toNat false
  iwin : pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat
  chunk : ∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true


structure PreUmS (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop where
  ret : RetOK s
  r0 : s.regs 0 = z
  r3 : s.regs 3 = pI
  r1 : s.regs 1 = nI
  mod : Mod C R R2 T L
  env : Env C R R2 T b L lo hi s
  lo4 : lo + 4904 ≤ (s.regs 4).toNat
  hi4 : (s.regs 4).toNat + 24 ≤ hi
  cost : roundupsize nI.toNat true ≤ b
  stWin : Outside st 2048 [(lo, hi)]
  stRt : Outside st 2048 R.rt
  stPriv : Outside st 2048 R2.priv
  stZ : Outside st 2048 [(z.toNat, z.toNat + 32)]
  mult : MultOK C z.toNat lo hi s.mem
  multRt : Outside C.mulTab 40 R.rt
  multK : ∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt
  eofA : s.mem.accessible C.ioEOF 16 false = true
  eofW : Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]
  eofR : Outside C.ioEOF 16 R.rt
  bigA : s.mem.accessible C.errBig 16 false = true
  bigW : Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]
  bigR : Outside C.errBig 16 R.rt
  init : Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem
  maxA : s.mem.accessible C.maxStr 78 false = true
  maxW : Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]
  maxR : Outside C.maxStr 78 R.rt
  maxB : ∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k
  zbuf : Buffer s z 32 true
  zwin : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat
  zR : Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L
  zP : Outside z.toNat 32 R2.priv
  zS : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]
  zg : (s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16
  ibuf : Buffer s pI nI.toNat false
  iwin : pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat
  chunk : ∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true


/-- the entry precondition as a plain conjunction (no consumer structure in the statement) -/
def PreU (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  (RetOK s) ∧
  (s.regs 0 = z) ∧
  (s.regs 3 = pI) ∧
  (s.regs 1 = nI) ∧
  (Mod C R R2 T L) ∧
  (Env C R R2 T b L lo hi s) ∧
  (lo + 4904 ≤ (s.regs 4).toNat) ∧
  ((s.regs 4).toNat + 24 ≤ hi) ∧
  (R.ok sb [(s.regs 4).toNat - 72, pI.toNat, nI.toNat]) ∧
  (R.ok sb [(s.regs 4).toNat - 40, pI.toNat, nI.toNat]) ∧
  (roundupsize nI.toNat true ≤ b) ∧
  (Outside st 2048 [(lo, hi)]) ∧
  (Outside st 2048 R.rt) ∧
  (Outside st 2048 R2.priv) ∧
  (Outside st 2048 [(z.toNat, z.toNat + 32)]) ∧
  (MultOK C z.toNat lo hi s.mem) ∧
  (Outside C.mulTab 40 R.rt) ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  (s.mem.accessible C.ioEOF 16 false = true) ∧
  (Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.ioEOF 16 R.rt) ∧
  (s.mem.accessible C.errBig 16 false = true) ∧
  (Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.errBig 16 R.rt) ∧
  (Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) ∧
  (s.mem.accessible C.maxStr 78 false = true) ∧
  (Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.maxStr 78 R.rt) ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  (Buffer s z 32 true) ∧
  (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧
  (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  (Outside z.toNat 32 R2.priv) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  (Buffer s pI nI.toNat false) ∧
  (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧     blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

theorem PreU.toS {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreU C sb st R R2 T b L lo hi z pI nI s) :
    PreUS C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨ret, r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨ret, r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

theorem PreU.of0 {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (hr : RetOK s) (h : PreU0 C sb st R R2 T b L lo hi z pI nI s) :
    PreU C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨hr, r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

/-- `RetOK` from `PreU0` and the ABI facts of the call (`X15 = 0`, `DF = 0`, `[RSP] < 2^47`) -/
theorem PreU0.retOK {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreU0 C sb st R R2 T b L lo hi z pI nI s)
    (hx : s.xmm 15 = 0) (hdf : s.df = false) (hret : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) : RetOK s := by
  obtain ⟨-, -, -, -, env, lo4, hi4, -⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := env
  exact ⟨Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega), hret, hx, hdf⟩

def PreUm (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  (RetOK s) ∧
  (s.regs 0 = z) ∧
  (s.regs 3 = pI) ∧
  (s.regs 1 = nI) ∧
  (Mod C R R2 T L) ∧
  (Env C R R2 T b L lo hi s) ∧
  (lo + 4904 ≤ (s.regs 4).toNat) ∧
  ((s.regs 4).toNat + 24 ≤ hi) ∧
  (roundupsize nI.toNat true ≤ b) ∧
  (Outside st 2048 [(lo, hi)]) ∧
  (Outside st 2048 R.rt) ∧
  (Outside st 2048 R2.priv) ∧
  (Outside st 2048 [(z.toNat, z.toNat + 32)]) ∧
  (MultOK C z.toNat lo hi s.mem) ∧
  (Outside C.mulTab 40 R.rt) ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  (s.mem.accessible C.ioEOF 16 false = true) ∧
  (Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.ioEOF 16 R.rt) ∧
  (s.mem.accessible C.errBig 16 false = true) ∧
  (Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.errBig 16 R.rt) ∧
  (Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) ∧
  (s.mem.accessible C.maxStr 78 false = true) ∧
  (Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.maxStr 78 R.rt) ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  (Buffer s z 32 true) ∧
  (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧
  (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  (Outside z.toNat 32 R2.priv) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  (Buffer s pI nI.toNat false) ∧
  (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧     blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

theorem PreUm.toS {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreUm C sb st R R2 T b L lo hi z pI nI s) :
    PreUmS C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨ret, r0, r3, r1, mod, env, lo4, hi4, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨ret, r0, r3, r1, mod, env, lo4, hi4, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

theorem PreU0m.add {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreU0m C sb st R R2 T b L lo hi z pI nI s) (ho : OkOut sb R pI nI s) :
    PreU0 C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨r0, r3, r1, mod, env, lo4, hi4, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨r0, r3, r1, mod, env, lo4, hi4, ho.1, ho.2, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

theorem PreUm.of0 {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (hr : RetOK s) (h : PreU0m C sb st R R2 T b L lo hi z pI nI s) :
    PreUm C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨r0, r3, r1, mod, env, lo4, hi4, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨hr, r0, r3, r1, mod, env, lo4, hi4, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

theorem PreU0m.retOK {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreU0m C sb st R R2 T b L lo hi z pI nI s)
    (hx : s.xmm 15 = 0) (hdf : s.df = false) (hret : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) : RetOK s := by
  obtain ⟨-, -, -, -, env, lo4, hi4, -⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := env
  exact ⟨Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega), hret, hx, hdf⟩


theorem PreU0.toM {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreU0 C sb st R R2 T b L lo hi z pI nI s) :
    PreU0m C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨r0, r3, r1, mod, env, lo4, hi4, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

theorem PreU0.okOut {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreU0 C sb st R R2 T b L lo hi z pI nI s) : OkOut sb R pI nI s := by
  obtain ⟨r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  exact ⟨okH, okD⟩

/-- keeps a disjunctive hypothesis away from `omega` -/
def Hide (P : Prop) : Prop := P
theorem Hide.mk {P : Prop} (h : P) : Hide P := h
theorem Hide.get {P : Prop} (h : Hide P) : P := h

/-- `TopPre` of the `SetFromDecimal` call, from the state `S3` at the call (return address pushed at `sp - 104`).  The string is
the copy `(pS, nI)`; `L'`/`b'` the live set and budget after the copy; the window of the callee is `[lo, hi3)`. -/
theorem toppre_dec {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b b' : Nat} {L L' : List (Nat × Nat)} {lo hi hi3 : Nat}
    {z pI nI pS : BitVec 64} {s S3 : State}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s) (hh3 : hi3 ≤ hi) (hh3' : (s.regs 4).toNat - 72 ≤ hi3)
    (hr0 : S3.regs 0 = z) (hr3 : S3.regs 3 = pS) (hr1 : S3.regs 1 = nI) (hr4 : S3.regs 4 = s.regs 4 - 104#64)
    (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hret : S3.mem.readLE ((s.regs 4).toNat - 104) 8 < 2 ^ 47)
    (hF : MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]))
    (hL : ∀ r ∈ L, r ∈ L') (hLw : ∀ r ∈ L', Outside r.1 (r.2 - r.1) [(lo, hi3)])
    (hLp : ∀ r ∈ L', Outside r.1 (r.2 - r.1) R2.priv)
    (hstr : pS.toNat + nI.toNat ≤ 2 ^ 48 ∧ (nI.toNat = 0 ∨ S3.mem.accessible pS.toNat nI.toNat false = true))
    (hswin : nI.toNat = 0 ∨ pS.toNat + nI.toNat ≤ lo ∨ hi3 ≤ pS.toNat)
    (hsz : nI.toNat = 0 ∨ pS.toNat + nI.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat)
    (hsR : nI.toNat = 0 ∨ Outside pS.toNat nI.toNat R.rt ∨ InRanges pS.toNat nI.toNat L')
    (hsP : nI.toNat = 0 ∨ Outside pS.toNat nI.toNat R2.priv)
    (hb' : b' = b - roundupsize nI.toNat true)
    (hInv : R.inv b' L' (S3.regs 14).toNat (view R.rt L' S3.mem)) :
    TopPre C R R2 T b' L' lo hi3 z pS nI S3 := by
  have hswinH := Hide.mk hswin
  have hszH := Hide.mk hsz
  have hsRH := Hide.mk hsR
  have hsPH := Hide.mk hsP
  have hstrH := Hide.mk hstr
  clear hswin hsz hsR hsP hstr
  have hp := hpre.toS
  obtain ⟨hRet, -, -, -, hMod, hEnv, hlo, hhi, -, -, hcost, -, -, -, -, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo, hMr, hMb,
    hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hchunk⟩ := hp
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp : (S3.regs 4).toNat = (s.regs 4).toNat - 104 := by
    rw [hr4]; have := (s.regs 4).isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e3s : hi3 ≤ 2 ^ 48 := by omega
  have e9s : Outside lo (hi3 - lo) R.rt := Outside.of_sub e9 (Nat.le_refl _) (by omega)
  have e10s : Outside lo (hi3 - lo) R2.priv := Outside.of_sub e10 (Nat.le_refl _) (by omega)
  have e13s : (s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi3 ≤ (s.regs 14).toNat + 16 := by omega
  have e14s : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(lo, hi3)] := by
    intro r hr
    have := e14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  have e5s : s.mem.accessible lo (hi3 - lo) true = true :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hrt : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S3.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    exact hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have hlaws := Mod.laws C hMod
  have hpriv := Mod.priv C hMod
  have hw1 : (Janus.Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 104) 8 false = true) :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
  have hWinZ : z.toNat + 32 ≤ lo ∨ hi3 ≤ z.toNat := by omega
  unfold TopPre
  refine ⟨?_, hr0, hr3, hr1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RetOK
    rw [hsp, hF.accessible]
    exact ⟨hw1, hret, hx15, hdf⟩
  · exact Mod.extL C hMod hLp
  · -- Env
    have hgz : (S3.regs 14).toNat = (s.regs 14).toNat := by rw [hr14]
    refine ⟨by omega, by omega, e3s, by omega, ?_, by rw [hgz]; exact e6, ?_, ?_, e9s, e10s, by rw [hgz]; exact e11,
      by rw [hgz]; exact e12, by rw [hgz]; exact e13s, e14s, ?_, ?_, hInv, hLw⟩
    · rw [hF.accessible]; exact e5s
    · rw [hgz, hF.accessible]; exact e7
    · rw [hgz, hrt _ _ e11 (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact e8
    · refine StaticOK.frame e15 hF ?_
      intro r hr
      rw [outside_append]
      exact ⟨(Mod.static C hMod) r hr, e14 r hr⟩
    · rw [hr14]; refine hlaws.env_frame _ _ _ e16 (Janus.Spec.Map.Agrees.of_memFrame hF ?_)
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have a1 := MemFrame.outside_mem e10 hr
      have a2 : Outside a 1 R.rt := Outside.of_sub (hpriv r hr) h1 (by omega)
      rw [outside_append]
      refine ⟨a2, ?_⟩
      simp only [outside_cons, outside_nil, and_true]
      omega
  · omega
  · omega
  · -- MultOK
    obtain ⟨u1, u2, u3⟩ := hMult
    have u2' := u2
    simp only [outside_cons, outside_nil, and_true] at u2'
    refine ⟨by rw [hF.accessible]; exact u1, ?_, ?_⟩
    · simp only [outside_cons, outside_nil, and_true]
      omega
    · intro k hk1 hk2
      obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
      have v4' := v4
      simp only [outside_cons, outside_nil, and_true] at v4'
      have hread : S3.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
        hrt _ _ (Outside.of_sub hMt (by omega) (by omega))
          (by simp only [outside_cons, outside_nil, and_true]; omega)
      rw [hread]
      have hMk' := hMk k hk1 hk2
      generalize s.mem.readLE (C.mulTab + 8 * k) 8 = pp at *
      refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, ?_⟩
      · have hv : S3.mem.readLE pp 32 = s.mem.readLE pp 32 :=
          hrt pp 32 hMk' (by simp only [outside_cons, outside_nil, and_true]; exact v4'.1)
        show S3.mem.readLE pp 32 = _
        rw [hv]
        exact v3
      · simp only [outside_cons, outside_nil, and_true]
        omega
  · rw [hF.accessible]; exact hE1
  · simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
    omega
  · rw [hF.accessible]; exact hB1
  · simp only [outside_cons, outside_nil, and_true] at hB2 ⊢
    omega
  · rw [hF.accessible]; exact hMa
  · simp only [outside_cons, outside_nil, and_true] at hMo ⊢
    omega
  · exact hMr
  · intro k hk
    rw [hrt _ _ (Outside.of_sub hMr (by omega) (by omega)) (by
      simp only [outside_cons, outside_nil, and_true] at hMo ⊢
      omega)]
    exact hMb k hk
  · -- Buffer z
    obtain ⟨b1, b2⟩ := hzbuf
    exact ⟨b1, by rw [hF.accessible]; exact b2⟩
  · exact hWinZ
  · rcases hzR with h | h
    · exact Or.inl h
    · exact Or.inr (InRanges.of_subset h hL)
  · exact hzP
  · exact hzS
  · rw [hr14]; exact hzg
  · exact ⟨hstrH.get.1, hstrH.get.2⟩
  · exact hswinH.get
  · exact hszH.get
  · -- ChunkAll
    intro sp sl h1 h2 h3 h4
    have hb48 := hstrH.get.1
    have hsp' : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
    have hsl' : (BitVec.ofNat 64 sl).toNat = sl := Nat.mod_eq_of_lt (by omega)
    have hc := hchunk sl h3 h4 (by omega)
    have hn0 : nI.toNat ≠ 0 := by omega
    have hsR' := hsRH.get.resolve_left hn0
    have hsP' := hsPH.get.resolve_left hn0
    have hbs : blockSize sl true + blockSize 48 false ≤ b' := by
      rw [hb']; exact hc.2.2
    unfold ChunkOK
    rw [hsp', hsl']
    refine ⟨hc.1, fun q => hc.2.1 q sp, hbs, ?_, by omega, by have := hswinH.get; omega, ?_, ?_⟩
    · rcases hstrH.get.2 with h0 | h0
      · omega
      · exact Janus.Arm64.Memory.accessible_sub S3.mem h0 (Or.inl rfl) h1 (by omega)
    · rcases hsR' with h | h
      · exact Or.inl (Outside.of_sub h h1 (by omega))
      · exact Or.inr (InRanges.sub h h1 (by omega))
    · exact Outside.of_sub hsP' h1 (by omega)

end Fv256.Amd64.UnmarshalSpec
