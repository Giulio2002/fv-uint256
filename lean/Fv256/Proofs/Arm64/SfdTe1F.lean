import Fv256.Proofs.Arm64.SfdTeObj0

/-!
# `strconv.toError`, write-barrier branch (arm64): the facts at the entry of `gcWriteBarrier2`

`Pre1`: everything the prefix (entry up to the call of `runtime.gcWriteBarrier2`) establishes, as the interface between the
prefix lemma `te1_pre` and the tail `te_tail1` (so that each is a small separate declaration).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

structure Pre1 (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (s S : State) (m' m2 m3 m4 : Janus.Arm64.Memory) (q t : BitVec 64) : Prop where
  hdep : R2.depth ≤ 4096
  hlow : 4192 ≤ s.sp.toNat
  e9 : Outside (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) R.rt
  e10 : Outside (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) R2.priv
  hSf : MemFrame s.mem S.mem [(s.sp.toNat - (R2.depth + 96), s.sp.toNat + 72)]
  hfr : MemFrame S.mem m' (R2.priv ++ [(s.sp.toNat - 96 - R2.depth, s.sp.toNat - 96 - 8),
        (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 24)])
  hMF1 : MemFrame m' m2 (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8), (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 24)])
  hMF2 : MemFrame (m2.writeLE (s.sp.toNat - 16) 8 q.toNat) m3
        (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8), (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 24)] ++
          [(q.toNat, q.toNat + sl.toNat)])
  hMF3 : MemFrame ((m3.writeLE (s.sp.toNat - 40) 8 sl.toNat).writeLE (s.sp.toNat - 24) 8 q.toNat) m4
        (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8), (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 8)])
  hLF1 : LiveFrame m' m2 L []
  hLF3 : LiveFrame ((m3.writeLE (s.sp.toNat - 40) 8 sl.toNat).writeLE (s.sp.toNat - 24) 8 q.toNat) m4
        (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)]) []
  hCop : Mem.Copied (m2.writeLE (s.sp.toNat - 16) 8 q.toNat) m3 q.toNat sp.toNat sl.toNat
  hinvN : R.inv (b - blockSize sl.toNat true - 48)
        (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) (s.regs 28).toNat
        (view R.rt (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) m4)
  hInR : InRanges q.toNat (blockSize sl.toNat true) R.rt
  hInT : InRanges t.toNat (blockSize 48 false) R.rt
  hApL : ApartAll q.toNat (blockSize sl.toNat true) L
  hApT : ApartAll t.toNat 48 L ∧ Apart t.toNat 48 q.toNat (blockSize sl.toNat true)
  hQsl : sl.toNat ≤ blockSize sl.toNat true
  hspR : Outside sp.toNat sl.toNat R.rt ∨ InRanges sp.toNat sl.toNat L
  hspP : Outside sp.toNat sl.toNat R2.priv
  hsdisj : sp.toNat + sl.toNat ≤ s.sp.toNat - 4192 ∨ s.sp.toNat + 72 ≤ sp.toNat
  hSm8 : S.mem.readLE (s.sp.toNat + 8) 8 = fp.toNat
  oE : Outside strconvErrSyntax 16 [(s.sp.toNat - 4192, s.sp.toNat + 72)]
  pE : Outside strconvErrSyntax 16 R.rt
  qE : Outside strconvErrSyntax 16 R2.priv
  hf4 : m4.readLE wbFlag 4 ≠ 0
  hacc4 : m4.accessible wbFlag 4 false = true
  hacc4t : m4.accessible t.toNat 48 true = true
  hacc4e : m4.accessible strconvErrSyntax 16 false = true
  hacc4w : m4.accessible (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) true = true
  hlr4 : m4.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat
  hfp4 : m4.readLE (s.sp.toNat - 96 - 8) 8 = (s.regs 29).toNat
  hts4 : s.sp.toNat - 4192 + (s.sp.toNat + 72 - (s.sp.toNat - 4192)) ≤ t.toNat ∨ t.toNat + 48 ≤ s.sp.toNat - 4192
  hte4 : strconvErrSyntax + 16 ≤ t.toNat ∨ t.toNat + 48 ≤ strconvErrSyntax
  hwF : wbFlag + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ wbFlag
  hL18 : ∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4192, s.sp.toNat + 72)]
  hrt0 : ∀ r ∈ R.rt, 0 < r.1
  hal : s.sp.toNat % 16 = 0
  hsp72 : s.sp.toNat + 72 ≤ 2 ^ 48
  e5 : s.mem.accessible (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) true = true
  pW : Outside wbFlag 4 R.rt
  qW : Outside wbFlag 4 R2.priv
  hSrec : S.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
    S.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8
  oW : Outside wbFlag 4 [(s.sp.toNat - 4192, s.sp.toNat + 72)]

end Fv256.Arm64.SfdToError
