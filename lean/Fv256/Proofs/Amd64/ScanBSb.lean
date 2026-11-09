import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanBPre

/-!
# `Scan` (`[]byte` source): from the state after `runtime.slicebytetostring` to `SciPre` of the call of `scanScientificFromString` (Extracted-free)

Ported from the `UnmarshalText` decimal branch (`UnmarshalDec`, `UnmarshalSpec.toppre_dec`): the same frame layout, the call at `SP - 72`
(instead of `SP - 104`), the window of the callee `[lo, SP - 40)`.
-/

open Janus Janus.Contracts Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanBSb

variable (C : SfdCfg)

/-- the live additions of the contract, simplified -/
theorem adds_eq (c : Prop) [Decidable c] (n r0 : Nat) :
    (((if c then (if n = 0 then [] else [(r0, r0 + n)]) else []) ++
      (if c then [] else if n = 0 then [] else [(r0, r0 + n)])) : List (Nat × Nat)) =
    (if n = 0 then [] else [(r0, r0 + n)]) := by
  by_cases hc : c <;> by_cases hn : n = 0 <;> simp [hc, hn]

theorem loc {rt priv : List (Nat × Nat)} {buf st ptr n r0 lo hi hi3 z : Nat} {m0 : Janus.Arm64.Memory}
    {L : List (Nat × Nat)} (h : StrAt rt buf st ptr n r0 m0) (hn : 0 < n)
    (hb1 : lo ≤ buf) (hb2 : buf + 32 ≤ hi) (hh3 : hi3 ≤ buf) (hh3' : hi3 ≤ hi)
    (hwrt : Outside lo (hi - lo) rt) (hwp : Outside lo (hi - lo) priv)
    (hpwf : ∀ r ∈ priv, r.1 ≤ r.2) (hprt : ∀ r ∈ priv, Outside r.1 (r.2 - r.1) rt)
    (hstW : Outside st 2048 [(lo, hi)]) (hstP : Outside st 2048 priv) (hstZ : Outside st 2048 [(z, z + 32)])
    (hzw : z + 32 ≤ lo ∨ hi ≤ z) (hzL : Outside z 32 rt ∨ InRanges z 32 L)
    (hbuf : buf ≠ 0) (hfr : 32 < n → ApartAll r0 n L) :
    Outside r0 n [(lo, hi3)] ∧ Outside r0 n priv ∧ (r0 + n ≤ z ∨ z + 32 ≤ r0) := by
  rcases h with h0 | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, r, hr, hr1, hr2⟩
  · omega
  · have hb := Janus.Arm64.Memory.readLE_lt m0 ptr 1
    simp only [Nat.reducePow, Nat.pow_one] at hb
    have hs : r0 + n ≤ st + 2048 ∧ st ≤ r0 := by omega
    have := hstZ
    simp only [outside_cons, outside_nil, and_true] at this
    refine ⟨Outside.of_sub (rs := [(lo, hi3)]) ?_ hs.2 hs.1, Outside.of_sub hstP hs.2 hs.1, ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at hstW ⊢; omega
    · omega
  · subst h4
    refine ⟨?_, Outside.of_sub hwp hb1 (by omega), by omega⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  · have hin : InRanges r0 n rt := ⟨r, hr, hr1, hr2⟩
    have hw := MemFrame.outside_mem hwrt hr
    have hwin : r0 + n ≤ lo ∨ hi ≤ r0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [outside_cons, outside_nil, and_true]; omega
    · exact Fv256.Amd64.FromDecimalSpec.outside_of_in hin priv hpwf hprt
    · rcases hzL with hz | hz
      · have := InRanges.apart hin hz
        unfold Apart at this; omega
      · have := (hfr (by omega)).apart_of_inRanges hz
        omega


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

/-- keeps a disjunctive hypothesis away from `omega` -/
def Hide (P : Prop) : Prop := P
theorem Hide.mk {P : Prop} (h : P) : Hide P := h
theorem Hide.get {P : Prop} (h : Hide P) : P := h


/-- the entry facts of the `[]byte` case, as a structure (the fields of `ScanSpec.PreB`) -/
structure PreBS (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop where
  mod : Mod C R R2 T L
  env : Env C R R2 T b L lo hi s
  lo4 : lo + 4992 ≤ (s.regs 4).toNat
  hi4 : (s.regs 4).toNat + 32 ≤ hi
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
  chunk : ∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧ blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true

theorem PreBS.of {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : Fv256.Amd64.ScanSpec.PreB C sb st R R2 T b L lo hi z pI nI (viewS s pI nI)) :
    PreBS C sb st R R2 T b L lo hi z pI nI s := by
  have hv4 : (viewS s pI nI).regs 4 = s.regs 4 := by simp [viewS, setRegF_apply]
  have hv14 : (viewS s pI nI).regs 14 = s.regs 14 := by simp [viewS, setRegF_apply]
  obtain ⟨-, -, -, mod, env, lo4, hi4, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩ := h
  simp only [hv4, hv14] at env lo4 hi4 okD multK zg
  exact ⟨mod, env, lo4, hi4, okD, cost, stWin, stRt, stPriv, stZ, mult, multRt, multK, eofA, eofW, eofR, bigA, bigW, bigR, init, maxA, maxW, maxR, maxB, zbuf, zwin, zR, zP, zS, zg, ibuf, iwin, chunk⟩

/-- `TopPre` of the `SetFromDecimal` call, from the state `S3` at the call (return address pushed at `sp - 72`).  The string is
the copy `(pS, nI)`; `L'`/`b'` the live set and budget after the copy; the window of the callee is `[lo, hi3)`. -/
theorem toppre_dec {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b b' : Nat} {L L' : List (Nat × Nat)} {lo hi hi3 : Nat}
    {z pI nI pS : BitVec 64} {s S3 : State}
    (hpre : PreBS C sb st R R2 T b L lo hi z pI nI s) (hh3 : hi3 ≤ hi) (hh3' : (s.regs 4).toNat - 40 ≤ hi3)
    (hr0 : S3.regs 0 = z) (hr3 : S3.regs 3 = pS) (hr1 : S3.regs 1 = nI) (hr4 : S3.regs 4 = s.regs 4 - 72#64)
    (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hret : S3.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 47)
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
  have hp := hpre
  obtain ⟨hMod, hEnv, hlo, hhi, -, hcost, -, -, -, -, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo, hMr, hMb,
    hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hchunk⟩ := hp
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp : (S3.regs 4).toNat = (s.regs 4).toNat - 72 := by
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
  have hw1 : (Janus.Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 72) 8 false = true) :=
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


structure SbPost (R : RtInv) (st b : Nat) (L : List (Nat × Nat)) (s : State) (pI nI r0 r1 : BitVec 64)
    (M0 m : Janus.Arm64.Memory) (buf : Nat) : Prop where
  mf : MemFrame M0 m (R.rt ++ [((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72),
        ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 24)] ++
      (if buf = 0 then [] else [(buf, buf + 32)]))
  soa : (r1.toNat = (strBytes s.mem pI.toNat nI.toNat).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
      (0 < r1.toNat → s.mem.accessible r0.toNat r1.toNat false = true) ∧
      strBytes m r0.toNat r1.toNat = strBytes s.mem pI.toNat nI.toNat) ∧
      StrAt R.rt (buf) st pI.toNat r1.toNat r0.toNat M0
  lf : LiveFrame M0 m L (if buf = 0 then [] else [(buf, buf + 32)])
  fr : FreshFrom (if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L
  inv : R.inv (b - roundupsize nI.toNat true)
      (L ++ ((if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (s.regs 14).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) m)


theorem m0_frame {R : RtInv} {sb st : Nat} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} {M0 : Janus.Arm64.Memory} {v5 vt vd ra : Nat}
    (hpre : PreBS C sb st R R2 T b L lo hi z pI nI s)
    (hM0c : M0 = ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 vt).writeLE ((s.regs 4).toNat + 24) 8 vd).writeLE
      ((s.regs 4).toNat + 8) 8 z.toNat).writeLE ((s.regs 4).toNat - 72) 8 ra) :
    MemFrame s.mem M0 [(lo, hi)] := by
  have hlo4 := hpre.lo4
  have hhi4 := hpre.hi4
  rw [hM0c]
  refine ((((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
    (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
    (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)

theorem dec_call_pre {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {retv v5 vt vd ra : Nat}
    (hpre : PreBS C sb st R R2 T b L lo hi z pI nI s)
    (hP : SbPost R st b L s pI nI r0 r1 M0 m ((s.regs 4).toNat - 40))
    (hM0c : M0 = ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 vt).writeLE ((s.regs 4).toNat + 24) 8 vd).writeLE
      ((s.regs 4).toNat + 8) 8 z.toNat).writeLE ((s.regs 4).toNat - 72) 8 ra)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8)) (hr3 : S3.regs 3 = r0) (hr1 : S3.regs 1 = r1) (hr4 : S3.regs 4 = s.regs 4 - 72#64)
    (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hS3 : S3.mem = m.writeLE ((s.regs 4).toNat - 72) 8 retv) (hretv : retv < 2 ^ 47) :
    TopPre C R R2 T (b - roundupsize nI.toNat true) (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]))
      lo ((s.regs 4).toNat - 40) z r0 nI S3 ∧
    (∀ k, k < nI.toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1) ∧
    MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
  obtain ⟨hMF, hSOA, hLF, hFr, hInv⟩ := hP
  have hbne0 : (s.regs 4).toNat - 40 ≠ 0 := by have := hpre.lo4; omega
  rw [if_neg hbne0] at hMF hLF
  obtain ⟨hSO, hSA⟩ := hSOA
  have hp := hpre
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hEnv := hp.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hn : r1.toNat = nI.toNat := by
    rw [hSO.1]; simp
  have hr1' : S3.regs 1 = nI := by rw [hr1]; exact BitVec.eq_of_toNat_eq hn
  have hM0 := m0_frame C hpre hM0c
  have hbne : (s.regs 4).toNat - 40 ≠ 0 := by omega
  have hzr : BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8) = z := by
    have ho : Outside ((s.regs 4).toNat + 8) 8 (R.rt ++ [((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72),
        ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 24)] ++ [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), ?_, ?_⟩, ?_⟩ <;> omega
    rw [hMF.readLE _ _ ho, hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt z.isLt
  rw [hzr] at hr0
  have hadds : ((if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])) =
      (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]) := by
    rw [Fv256.Amd64.ScanBSb.adds_eq, hn]
  rw [hadds] at hInv
  rw [hn] at hSO hSA
  -- the frame from the entry memory to the memory at the call
  have hwin2 : MemFrame M0 m (R.rt ++ [(lo, hi)]) := by
    refine MemFrame.mono hMF ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩ <;> omega
  have hF1 : MemFrame s.mem m (R.rt ++ [(lo, hi)]) := by
    refine hM0.trans hwin2 ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.2, h⟩
  have hF : MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
    rw [hS3]
    exact hF1.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hret : S3.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 47 := by
    rw [hS3, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hretv
  by_cases hz0 : nI.toNat = 0
  · -- empty input: nothing is read, nothing is added to the live set
    refine ⟨?_, fun k hk => absurd hk (by omega), hF⟩
    rw [if_pos hz0] at hInv ⊢
    have hInv' : R.inv (b - roundupsize nI.toNat true) (L ++ []) (S3.regs 14).toNat
        (view R.rt (L ++ []) S3.mem) := by
      rw [hr14, hS3]
      refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)])
        (MemFrame.of_writeLE m _ (r := ((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInv
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      left
      rcases hr with rfl
      exact Outside.of_sub e9 (by omega) (by simp only; omega)
    refine toppre_dec C hpre (hi3 := (s.regs 4).toNat - 40) (by omega) (by omega) hr0 hr3 hr1' hr4 hr14 hx15 hdf hret hF
      (L' := L ++ []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hInv'
    · exact fun r hr => List.mem_append_left _ hr
    · intro r hr
      have h := e18 r (by simpa using hr)
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega
    · intro r hr
      exact Mod.lpriv C hp.mod r (by simpa using hr)
    · exact ⟨by have := hSO.2.1; omega, Or.inl hz0⟩
    · exact Or.inl hz0
    · exact Or.inl hz0
    · exact Or.inl hz0
    · exact Or.inl hz0
    · rfl
  · have hpos : 0 < nI.toNat := Nat.pos_of_ne_zero hz0
    have hfr : 32 < nI.toNat → ApartAll r0.toNat nI.toNat L := by
      intro h32
      have := hFr
      rw [hn] at this
      rw [if_pos (by omega), if_neg hz0] at this
      simpa using this _ (List.mem_singleton_self _)
    obtain ⟨hlw, hlp, hlz⟩ := Fv256.Amd64.ScanBSb.loc (hi3 := (s.regs 4).toNat - 40) hSA hpos (by omega) (by omega)
      (Nat.le_refl _) (by omega) e9 e10 hp.init.2.2.2.2 (Mod.priv C hp.mod) hp.stWin hp.stPriv hp.stZ hp.zwin hp.zR hbne hfr
    rw [if_neg hz0] at hInv ⊢
    have hInv' : R.inv (b - roundupsize nI.toNat true) (L ++ [(r0.toNat, r0.toNat + nI.toNat)]) (S3.regs 14).toNat
        (view R.rt (L ++ [(r0.toNat, r0.toNat + nI.toNat)]) S3.mem) := by
      rw [hr14, hS3]
      refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)])
        (MemFrame.of_writeLE m _ (r := ((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInv
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      left
      rcases hr with rfl
      exact Outside.of_sub e9 (by omega) (by simp only; omega)
    have hlw2 : r0.toNat + nI.toNat ≤ lo ∨ (s.regs 4).toNat - 40 ≤ r0.toNat := by
      have h := hlw
      simp only [outside_cons, outside_nil, and_true] at h
      exact h
    have hbytes : ∀ k, k < nI.toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1 := by
      intro k hk
      have hq := congrArg (fun l => l.getD k 0) hSO.2.2.2
      rw [strBytes_getD _ _ _ _ (by omega), strBytes_getD _ _ _ _ (by omega)] at hq
      rw [hS3]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one]
      exact hq
    refine ⟨?_, hbytes, hF⟩
    refine toppre_dec C hpre (hi3 := (s.regs 4).toNat - 40) (by omega) (by omega) hr0 hr3 hr1' hr4 hr14 hx15 hdf hret hF
      (L' := L ++ [(r0.toNat, r0.toNat + nI.toNat)]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hInv'
    · exact fun r hr => List.mem_append_left _ hr
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · have := e18 r h
        simp only [outside_cons, outside_nil, and_true] at this ⊢
        omega
      · simp only [List.mem_singleton] at h
        subst h
        rw [Nat.add_sub_cancel_left]; exact hlw
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact Mod.lpriv C hp.mod r h
      · simp only [List.mem_singleton] at h
        subst h
        rw [Nat.add_sub_cancel_left]; exact hlp
    · refine ⟨by have := hSO.2.1; omega, Or.inr ?_⟩
      rw [hF.accessible]; exact hSO.2.2.1 hpos
    · right
      simp only [outside_cons, outside_nil, and_true] at hlw
      exact hlw
    · exact Or.inr hlz
    · exact Or.inr (Or.inr ⟨(r0.toNat, r0.toNat + nI.toNat), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
    · exact Or.inr hlp
    · rfl



/-- the read-only data stays loaded across a memory frame on writable ranges that keeps the regions (no `r.1 ≤ r.2` needed) -/
theorem dl_frame' {P : Janus.Amd64.Program} {m m' : Janus.Arm64.Memory} {rs : List (Nat × Nat)}
    (h : P.DataLoaded m) (hr : m'.regions = m.regions) (hf : MemFrame m m' rs)
    (hw : ∀ r ∈ rs, m.accessible r.1 (r.2 - r.1) true = true) : P.DataLoaded m' := by
  intro d hd
  obtain ⟨hreg, hb⟩ := h d hd
  refine ⟨by rw [show m'.regions = m.regions from hr]; exact hreg, fun i hi => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have hout : Outside (P.data[k].base + i) 1 rs := by
    refine outside_of_all rs (fun r hr' => ?_)
    have hdis := Janus.Amd64.Tactic.disjoint_of_dataLoaded h k hk (hw r hr')
    omega
  have := hf.readLE (P.data[k].base + i) 1 hout
  simp only [Janus.Arm64.Memory.readLE_one] at this
  rw [show (m'.bytes (P.data[k].base + i)).toNat = (m.bytes (P.data[k].base + i)).toNat from this]
  exact hb i hi

set_option maxRecDepth 100000 in
/-- the pages of the copy made by `slicebytetostring` are readable -/
theorem pageR_sub {m : Janus.Arm64.Memory} {a l p n : Nat} (h : Fv256.IndexByte.PageReadable m a l) (hn : 0 < n)
    (h1 : a ≤ p) (h2 : p + n ≤ a + l) : Fv256.IndexByte.PageReadable m p n := by
  unfold Fv256.IndexByte.PageReadable at h ⊢
  rcases h with h | ⟨h3, h4⟩
  · omega
  · right
    refine ⟨by omega, Janus.Arm64.Memory.accessible_sub m h4 (Or.inl rfl) (by omega) (by omega)⟩


/-- `TlsG`, `InitDone` and the TLS slot survive the `slicebytetostring` call (frame `R.rt ++ window`) -/
theorem tls_frame2 {R : RtInv} {R2 : IfaceModel} {lo hi hi3 : Nat} {dst : BitVec 64} {s S : State}
    (hF : MemFrame s.mem S.mem (R.rt ++ [(lo, hi)]))
    (hfs : S.fsBase = s.fsBase) (h14 : S.regs 14 = s.regs 14) (hh3 : hi3 ≤ hi)
    (heofW : Outside C.ioEOF 16 [(lo, hi), (dst.toNat, dst.toNat + 32)]) (heofR : Outside C.ioEOF 16 R.rt)
    (hbigW : Outside C.errBig 16 [(lo, hi), (dst.toNat, dst.toNat + 32)]) (hbigR : Outside C.errBig 16 R.rt)
    (htls : TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem ∧
      Outside (s.fsBase.toNat - 8) 8 R.rt) :
    TlsG S ∧ Outside (S.fsBase.toNat - 8) 8 [(lo, hi3)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone C R2 S.mem := by
  obtain ⟨hT, ho, hi0, hor⟩ := htls
  have ho' := ho
  simp only [outside_cons, outside_nil, and_true] at ho' heofW hbigW
  have hso : Outside (s.fsBase.toNat - 8) 8 (R.rt ++ [(lo, hi)]) := by
    rw [outside_append]; exact ⟨hor, by simp only [outside_cons, outside_nil, and_true]; exact ho'⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hfs]; exact hT.base
  · rw [hfs, hF.accessible]; exact hT.readable
  · rw [hfs, hF.readLE _ _ hso, h14]; exact hT.g
  · rw [hfs]; simp only [outside_cons, outside_nil, and_true]; omega
  · obtain ⟨i1, i2, i3, i4, i5⟩ := hi0
    have r1 : ∀ a, (a = C.ioEOF ∨ a = C.ioEOF + 8 ∨ a = C.errBig ∨ a = C.errBig + 8) → S.mem.readLE a 8 = s.mem.readLE a 8 := by
      intro a ha
      refine hF.readLE a 8 ?_
      rw [outside_append]
      refine ⟨?_, ?_⟩
      · rcases ha with rfl | rfl | rfl | rfl
        · exact Outside.of_sub heofR (Nat.le_refl _) (by omega)
        · exact Outside.of_sub heofR (by omega) (by omega)
        · exact Outside.of_sub hbigR (Nat.le_refl _) (by omega)
        · exact Outside.of_sub hbigR (by omega) (by omega)
      · simp only [outside_cons, outside_nil, and_true]
        rcases ha with rfl | rfl | rfl | rfl <;> omega
    refine ⟨?_, ?_, ?_, ?_, i5⟩
    · rw [r1 _ (Or.inl rfl)]; exact i1
    · rw [r1 _ (Or.inr (Or.inl rfl))]; exact i2
    · rw [r1 _ (Or.inr (Or.inr (Or.inl rfl)))]; exact i3
    · rw [r1 _ (Or.inr (Or.inr (Or.inr rfl)))]; exact i4

end Fv256.Amd64.ScanBSb
