import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.Amd64.UnmarshalSpec
import Fv256.Amd64.UnmarshalHex
import Fv256.Amd64.FromHexLib
import Fv256.DecCongr

/-!
# `UnmarshalJSON` quoted path (amd64): `PreU` of the `UnmarshalText` call on the unquoted subslice (Extracted-free)

`UnmarshalJSON` of `"..."` calls `UnmarshalText(input[1:n-1])` with its own frame (return address at `sp - 80`).  The extra
runtime-contract facts for that call (`QPre`) are conditional on the input being quoted; `toppre_ut` builds `PreU` and
`HexEnv` for the call state.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalQ

variable (C : SfdCfg)

/-- the extra facts the inner `UnmarshalText` call needs (its frame sits `80` bytes lower; the runtime contract accepts the
copy of the unquoted subslice `(pI + 1, nI - 2)` into the buffers of that frame) -/
def QPre (sb : Nat) (R : RtInv) (b lo : Nat) (pI nI : BitVec 64) (s : State) : Prop :=
  lo + 4984 ≤ (s.regs 4).toNat ∧
  R.ok sb [(s.regs 4).toNat - 152, pI.toNat + 1, nI.toNat - 2] ∧
  R.ok sb [(s.regs 4).toNat - 120, pI.toNat + 1, nI.toNat - 2] ∧
  roundupsize (nI.toNat - 2) true ≤ b ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat - 2 → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ b - roundupsize (nI.toNat - 2) true)

theorem hexenv_frame {R : RtInv} {lo hi : Nat} {z : BitVec 64} {s S : State} (h : HexEnv R lo hi z s)
    (hF : MemFrame s.mem S.mem [(lo, hi)]) : HexEnv R lo hi z S := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := h
  have t3' := t3
  have t6' := t6
  simp only [outside_cons, outside_nil, and_true] at t3' t6'
  refine ⟨?_, by rw [hF.accessible]; exact t2, t3, t4, by rw [hF.accessible]; exact t5, t6, t7, ?_⟩
  · intro c hc
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact t1 c hc
  · intro e he
    have hb := Fv256.Amd64.FromHexLib.errAddrOf_bounds e
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact t8 e he

set_option maxHeartbeats 4000000 in
theorem toppre_ut {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI pI' nI' : BitVec 64} {s S : State}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s) (hq : QPre C sb R b lo pI nI s) (hn2 : 2 ≤ nI.toNat)
    (hr0 : S.regs 0 = z) (hr3 : S.regs 3 = pI') (hr1 : S.regs 1 = nI')
    (hp' : pI'.toNat = pI.toNat + 1) (hn' : nI'.toNat = nI.toNat - 2)
    (hr4 : S.regs 4 = s.regs 4 - 80#64)
    (hr14 : S.regs 14 = s.regs 14) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hret : S.mem.readLE ((s.regs 4).toNat - 80) 8 < 2 ^ 47)
    (hF : MemFrame s.mem S.mem [(lo, hi)]) :
    PreU C sb st R R2 T b L lo hi z pI' nI' S := by
  have hp := hpre.toS
  obtain ⟨hRet, -, -, -, hMod, hEnv, hlo, hhi, hokH, hokD, hcost, hstW, hstR, hstP, hstZ, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo, hMr, hMb,
    hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hchunk⟩ := hp
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp : (S.regs 4).toNat = (s.regs 4).toNat - 80 := by
    rw [hr4]; have := (s.regs 4).isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hgz : (S.regs 14).toNat = (s.regs 14).toNat := by rw [hr14]
  have hwin1 : Outside lo (hi - lo) [(lo, hi)] → False := by
    intro h; simp only [outside_cons, outside_nil, and_true] at h; omega
  have hrt : ∀ a n, Outside a n [(lo, hi)] → S.mem.readLE a n = s.mem.readLE a n := fun a n h => hF.readLE a n h
  have hw1 : (Janus.Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 80) 8 false = true) :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
  have hlaws := Mod.laws C hMod
  have hpriv := Mod.priv C hMod
  have hMu2 := hMult.2.1
  simp only [outside_cons, outside_nil, and_true] at hMu2
  have hibuf' := hibuf
  obtain ⟨ib1, ib2⟩ := hibuf'
  unfold PreU
  refine ⟨?_, hr0, hr3, hr1, hMod, ?_, ?_, ?_, ?_, ?_, ?_, hstW, hstR, hstP, hstZ, ?_, hMt, ?_, ?_, hE2, hE3, ?_, hB2, hB3, ?_, ?_,
    hMo, hMr, ?_, ?_, hzwin, hzR, hzP, hzS, ?_, ?_, ?_, ?_⟩
  · unfold RetOK
    rw [hsp, hF.accessible]
    exact ⟨hw1, hret, hx15, hdf⟩
  · -- Env
    refine ⟨by omega, by omega, e3, by omega, ?_, by rw [hgz]; exact e6, ?_, ?_, e9, e10, by rw [hgz]; exact e11,
      by rw [hgz]; exact e12, by rw [hgz]; exact e13, e14, ?_, ?_, ?_, e18⟩
    · rw [hF.accessible]; exact e5
    · rw [hgz, hF.accessible]; exact e7
    · rw [hgz, hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact e8
    · refine StaticOK.frame e15 hF ?_
      intro r hr
      have := e14 r hr
      exact this
    · rw [hr14]; refine hlaws.env_frame _ _ _ e16 (Janus.Spec.Map.Agrees.of_memFrame hF ?_)
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have a1 := MemFrame.outside_mem e10 hr
      simp only [outside_cons, outside_nil, and_true]
      omega
    · rw [hgz]
      refine RtInv.inv_frame' hF (fun r hr => Or.inl ?_) e17
      have : r = (lo, hi) := by simpa using hr
      subst this; exact e9
  · omega
  · omega
  · have : (S.regs 4).toNat - 72 = (s.regs 4).toNat - 152 := by omega
    rw [this, hp', hn']; exact q2
  · have : (S.regs 4).toNat - 40 = (s.regs 4).toNat - 120 := by omega
    rw [this, hp', hn']; exact q3
  · rw [hn']; exact q4
  · -- MultOK
    obtain ⟨u1, u2, u3⟩ := hMult
    have u2' := u2
    simp only [outside_cons, outside_nil, and_true] at u2'
    refine ⟨by rw [hF.accessible]; exact u1, u2, ?_⟩
    intro k hk1 hk2
    obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
    have v4' := v4
    simp only [outside_cons, outside_nil, and_true] at v4'
    have hread : S.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
      hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [hread]
    have hMk' := hMk k hk1 hk2
    generalize s.mem.readLE (C.mulTab + 8 * k) 8 = pp at *
    refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, v4⟩
    have hv : S.mem.readLE pp 32 = s.mem.readLE pp 32 :=
      hrt pp 32 (by simp only [outside_cons, outside_nil, and_true]; exact v4'.1)
    show S.mem.readLE pp 32 = _
    rw [hv]
    exact v3
  · intro k hk1 hk2
    have hMu2' := hMu2
    have hread : S.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
      hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [hread]; exact hMk k hk1 hk2
  · rw [hF.accessible]; exact hE1
  · rw [hF.accessible]; exact hB1
  · obtain ⟨i1, i2, i3, i4, i5⟩ := hInit
    have hE2' := hE2
    have hB2' := hB2
    simp only [outside_cons, outside_nil, and_true] at hE2' hB2'
    refine ⟨?_, ?_, ?_, ?_, i5⟩
    · rw [hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact i1
    · rw [hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact i2
    · rw [hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact i3
    · rw [hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact i4
  · rw [hF.accessible]; exact hMa
  · intro k hk
    have hMo' := hMo
    simp only [outside_cons, outside_nil, and_true] at hMo'
    rw [hrt _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hMb k hk
  · obtain ⟨b1, b2⟩ := hzbuf
    exact ⟨b1, by rw [hF.accessible]; exact b2⟩
  · rw [hr14]; exact hzg
  · unfold Buffer
    rw [hp', hn']
    refine ⟨by omega, ?_⟩
    rw [hF.accessible]
    exact Janus.Arm64.Memory.accessible_sub s.mem ib2 (Or.inl rfl) (by omega) (by omega)
  · rw [hp', hn']; omega
  · intro sl h1 h2 h3
    rw [hn'] at h3 ⊢
    exact q5 sl h1 h2 h3


/-- the postcondition of `UnmarshalText` on the string `(p, n)` of memory `m` -/
def UTP (R : RtInv) (R2 : IfaceModel) (lo hi : Nat) (z : BitVec 64) (p n : Nat) (m : Janus.Arm64.Memory) (s' : State) : Prop :=
  (IsHex m p n →
    (∀ v, parseHex (bytesAt m p) n = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
    (∀ e, parseHex (bytesAt m p) n = .error e →
      s'.regs 0 = BitVec.ofNat 64 (m.readLE (errAddrOf e) 8) ∧
      s'.regs 3 = BitVec.ofNat 64 (m.readLE (errAddrOf e + 8) 8))) ∧
  (¬ IsHex m p n →
    (∀ v, decParse (bytesAt m p) n = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
    (decParse (bytesAt m p) n = .eof →
      (s'.regs 0).toNat = m.readLE C.ioEOF 8 ∧ (s'.regs 3).toNat = m.readLE (C.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0) ∧
    (decParse (bytesAt m p) n = .range →
      (s'.regs 0).toNat = m.readLE C.errBig 8 ∧ (s'.regs 3).toNat = m.readLE (C.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 m z.toNat) ∧
    (∀ lo' len', decParse (bytesAt m p) n = .syntax lo' len' →
      s'.regs 0 = BitVec.ofNat 64 C.numErrItab)) ∧
  MemFrame m s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

theorem utp_frame {R : RtInv} {R2 : IfaceModel} {lo hi hi3 p n : Nat} {z : BitVec 64} {m m' : Janus.Arm64.Memory} {s' : State}
    (hF : MemFrame m m' [(lo, hi)]) (hEOF : Outside C.ioEOF 16 [(lo, hi)]) (hBIG : Outside C.errBig 16 [(lo, hi)])
    (hERR : Outside 5995344 96 [(lo, hi)]) (hz : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hin : p + n ≤ lo ∨ hi ≤ p)
    (hh3 : hi3 ≤ hi) (h : UTP C R R2 lo hi3 z p n m' s') : UTP C R R2 lo hi z p n m s' := by
  have hbytes : ∀ k, k < n → bytesAt m' p k = bytesAt m p k := by
    intro k hk
    unfold bytesAt
    exact hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hpc : parseHex (bytesAt m' p) n = parseHex (bytesAt m p) n := parseHex_congr _ _ _ hbytes
  have hdc : decParse (bytesAt m' p) n = decParse (bytesAt m p) n := decParse_congr _ _ _ hbytes
  have hhex : IsHex m' p n ↔ IsHex m p n := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)] at h2 h3
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      rw [← hF.readLE p 1 (by simp only [outside_cons, outside_nil, and_true]; omega)] at h2
      rw [← hF.readLE (p + 1) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)] at h3
      exact ⟨h1, h2, h3⟩
  have herr : ∀ e, m'.readLE (errAddrOf e) 8 = m.readLE (errAddrOf e) 8 ∧ m'.readLE (errAddrOf e + 8) 8 = m.readLE (errAddrOf e + 8) 8 := by
    intro e
    have hb := Fv256.Amd64.FromHexLib.errAddrOf_bounds e
    exact ⟨hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hERR ⊢; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hERR ⊢; omega)⟩
  have hio1 : m'.readLE C.ioEOF 8 = m.readLE C.ioEOF 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hEOF ⊢; omega)
  have hio2 : m'.readLE (C.ioEOF + 8) 8 = m.readLE (C.ioEOF + 8) 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hEOF ⊢; omega)
  have hbg1 : m'.readLE C.errBig 8 = m.readLE C.errBig 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hBIG ⊢; omega)
  have hbg2 : m'.readLE (C.errBig + 8) 8 = m.readLE (C.errBig + 8) 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hBIG ⊢; omega)
  have hv : Janus.Spec.val256 m' z.toNat = Janus.Spec.val256 m z.toNat := by
    unfold Janus.Spec.val256
    exact hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hA, hB, hC⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    obtain ⟨a1, a2⟩ := hA (hhex.2 hx)
    rw [hpc] at a1 a2
    refine ⟨a1, fun e he => ?_⟩
    have := a2 e he
    rw [(herr e).1, (herr e).2] at this
    exact this
  · intro hx
    obtain ⟨b1, b2, b3, b4⟩ := hB (fun hh => hx (hhex.1 hh))
    rw [hdc] at b1 b2 b3 b4
    refine ⟨b1, fun he => ?_, fun hr => ?_, b4⟩
    · have := b2 he
      rw [hio1, hio2] at this
      exact this
    · have := b3 hr
      rw [hbg1, hbg2, hv] at this
      exact this
  · refine MemFrame.trans hF hC ?_
    intro a k hk
    simp only [outside_append, outside_cons, outside_nil, and_true] at hk ⊢
    obtain ⟨⟨hr, hp⟩, hw, hz⟩ := hk
    exact ⟨by omega, ⟨hr, hp⟩, by omega, hz⟩


theorem env_shrink {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 : Nat} {s : State}
    (h : Env C R R2 T b L lo hi s) (hh : hi3 ≤ hi) (hs : (s.regs 4).toNat + 8 ≤ hi3) : Env C R R2 T b L lo hi3 s := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := h
  refine ⟨e1, hs, by omega, e4, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (Nat.le_refl _) (by omega), e6, e7, e8,
    Outside.of_sub e9 (Nat.le_refl _) (by omega), Outside.of_sub e10 (Nat.le_refl _) (by omega), e11, e12, by omega, ?_, e15, e16, e17, ?_⟩
  · intro r hr
    have := e14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  · intro r hr
    have := e18 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

theorem preU_shrink {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 : Nat}
    {z pI nI : BitVec 64} {s : State}
    (h : PreU C sb st R R2 T b L lo hi z pI nI s) (hh : hi3 ≤ hi) (hs : (s.regs 4).toNat + 24 ≤ hi3) :
    PreU C sb st R R2 T b L lo hi3 z pI nI s := by
  obtain ⟨ret, r0, r3, r1, mod, env, lo4, hi4, okH, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  have sh : ∀ {a n : Nat} {rs : List (Nat × Nat)}, Outside a n ((lo, hi) :: rs) → Outside a n ((lo, hi3) :: rs) := by
    intro a n rs h
    simp only [outside_cons] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, h2⟩
  refine ⟨ret, r0, r3, r1, mod, env_shrink C env hh (by omega), lo4, hs, okH, okD, cost, ?_, stRt, stPriv, stZ, ?_, multRt, multK, eofA,
    sh eofW, eofR, bigA, sh bigW, bigR, init, maxA, sh maxW, maxR, maxB, zbuf, by omega, zR, zP, zS, zg, ibuf, by omega, chunk⟩
  · have := sh (a := st) (n := 2048) (rs := []) stWin
    exact this
  · obtain ⟨u1, u2, u3⟩ := mult
    refine ⟨u1, sh u2, ?_⟩
    intro k hk1 hk2
    obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
    exact ⟨v1, v2, v3, sh v4⟩

theorem hexenv_shrink {R : RtInv} {lo hi hi3 : Nat} {z : BitVec 64} {s : State} (h : HexEnv R lo hi z s) (hh : hi3 ≤ hi) :
    HexEnv R lo hi3 z s := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := h
  have sh : ∀ {a n : Nat}, Outside a n [(lo, hi), (z.toNat, z.toNat + 32)] → Outside a n [(lo, hi3), (z.toNat, z.toNat + 32)] := by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  exact ⟨t1, t2, sh t3, t4, t5, sh t6, t7, t8⟩

end Fv256.Amd64.UnmarshalQ
