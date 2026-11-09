import Fv256.Proofs.Arm64.ScanSpec
import Fv256.Proofs.Arm64.ScanCall

/-!
# `Scan` (arm64), the `[]byte` case: from the state after `string(b)` to the entry facts of `scanScientificFromString`
(Extracted-free).  `loc`: where the result of `runtime.slicebytetostring` lives; `byt_top0`: `TopPre0` for the call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSpec

namespace Fv256.Arm64.ScanByt0

variable (C : SfdCfg)

/-- keeps a disjunctive hypothesis away from `omega` -/
def Hide (P : Prop) : Prop := P
theorem Hide.mk {P : Prop} (h : P) : Hide P := h
theorem Hide.get {P : Prop} (h : Hide P) : P := h

theorem outside_of_in {a n : Nat} {rt : List (Nat × Nat)} (hin : InRanges a n rt) (priv : List (Nat × Nat))
    (hw : ∀ r ∈ priv, r.1 ≤ r.2) (hp : ∀ r ∈ priv, Outside r.1 (r.2 - r.1) rt) : Outside a n priv := by
  obtain ⟨r', hr', h1, h2⟩ := hin
  apply Janus.Contracts.outside_of_forall
  intro r hr
  have := MemFrame.outside_mem (hp r hr) hr'
  have := hw r hr
  omega

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
    · exact outside_of_in hin priv hpwf hprt
    · rcases hzL with hz | hz
      · have := InRanges.apart hin hz
        unfold Apart at this; omega
      · have := (hfr (by omega)).apart_of_inRanges hz
        omega


/-- `TopPre0` of the `scanScientificFromString` call from the state `S2` after `string(b)` (the copy `(pS, nI)`); `L'`/`b'` the live
set and budget after the copy, the callee's window `[lo, hi3)` with `hi3` the copy buffer or lower. -/
theorem byt_top0 {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b b' : Nat} {L L' : List (Nat × Nat)} {lo hi hi3 : Nat}
    {z pI nI pS : BitVec 64} {s S2 : State}
    (hpre : PreB C sb st R R2 T b L lo hi z pI nI s) (hlo : lo + 4720 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hh3 : hi3 ≤ s.sp.toNat - 40) (hh3' : s.sp.toNat - 48 ≤ hi3)
    (hr0 : S2.regs 0 = z) (hr1 : S2.regs 1 = pS) (hr2 : S2.regs 2 = nI) (hsp2 : S2.sp = s.sp - 80#64)
    (hr28 : S2.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S2.mem (R.rt ++ [(lo, hi)]))
    (hL : ∀ r ∈ L, r ∈ L') (hLw : ∀ r ∈ L', Outside r.1 (r.2 - r.1) [(lo, hi3)])
    (hLp : ∀ r ∈ L', Outside r.1 (r.2 - r.1) R2.priv)
    (hstr : pS.toNat + nI.toNat ≤ 2 ^ 48 ∧ (nI.toNat = 0 ∨ S2.mem.accessible pS.toNat nI.toNat false = true))
    (hswin : nI.toNat = 0 ∨ pS.toNat + nI.toNat ≤ lo ∨ hi3 ≤ pS.toNat)
    (hsz : nI.toNat = 0 ∨ pS.toNat + nI.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat)
    (hsR : nI.toNat = 0 ∨ Outside pS.toNat nI.toNat R.rt ∨ InRanges pS.toNat nI.toNat L')
    (hsP : nI.toNat = 0 ∨ Outside pS.toNat nI.toNat R2.priv)
    (hb' : b' = b - roundupsize nI.toNat true)
    (hInv : R.inv b' L' (S2.regs 28).toNat (view R.rt L' S2.mem)) :
    TopPre0 C R R2 T b' L' lo hi3 z pS nI S2 := by
  have hswinH := Hide.mk hswin
  have hszH := Hide.mk hsz
  have hsRH := Hide.mk hsR
  have hsPH := Hide.mk hsP
  have hstrH := Hide.mk hstr
  clear hswin hsz hsR hsP hstr
  obtain ⟨hMod, hEnv, hok, hcost, hstW, hstR, hstP, hstZ, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo, hMr, hMb,
    hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hRW, hchunk⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp : S2.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp2]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e3s : hi3 ≤ 2 ^ 48 := by omega
  have e9s : Outside lo (hi3 - lo) R.rt := Outside.of_sub e9 (Nat.le_refl _) (by omega)
  have e10s : Outside lo (hi3 - lo) R2.priv := Outside.of_sub e10 (Nat.le_refl _) (by omega)
  have e13s : (s.regs 28).toNat + 16 + 8 ≤ lo ∨ hi3 ≤ (s.regs 28).toNat + 16 := by omega
  have e14s : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(lo, hi3)] := by
    intro r hr
    have := e14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  have e5s : s.mem.accessible lo (hi3 - lo) true = true :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hrt : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    exact hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have hWinZ : z.toNat + 32 ≤ lo ∨ hi3 ≤ z.toNat := by omega
  have hMod' := hMod
  obtain ⟨hlaws, hd1, hd2, hIT, hpriv, -, hrtpos, hstatic, hstaticP, hok1, hok2, hok3, hTfact⟩ := hMod'
  unfold TopPre0
  refine ⟨hr0, hr1, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hlaws, hd1, hd2, hIT, hpriv, hLp, hrtpos, hstatic, hstaticP, hok1, hok2, hok3, hTfact⟩
  · -- Env
    have hgz : (S2.regs 28).toNat = (s.regs 28).toNat := by rw [hr28]
    refine ⟨by omega, by omega, e3s, by omega, ?_, by rw [hgz]; exact e6, ?_, ?_, e9s, e10s, by rw [hgz]; exact e11,
      by rw [hgz]; exact e12, by rw [hgz]; exact e13s, e14s, ?_, ?_, hInv, hLw⟩
    · rw [hF.accessible]; exact e5s
    · rw [hgz, hF.accessible]; exact e7
    · rw [hgz, hrt _ _ e11 (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact e8
    · refine StaticOK.frame e15 hF ?_
      intro r hr
      rw [outside_append]
      exact ⟨hstatic r hr, e14 r hr⟩
    · rw [hr28]; refine hlaws.env_frame _ _ _ e16 (Janus.Spec.Map.Agrees.of_memFrame hF ?_)
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
      have hread : S2.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
        hrt _ _ (Outside.of_sub hMt (by omega) (by omega))
          (by simp only [outside_cons, outside_nil, and_true]; omega)
      rw [hread]
      have hMk' := hMk k hk1 hk2
      generalize s.mem.readLE (C.mulTab + 8 * k) 8 = pp at *
      refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, ?_⟩
      · have hv : S2.mem.readLE pp 32 = s.mem.readLE pp 32 :=
          hrt pp 32 hMk' (by simp only [outside_cons, outside_nil, and_true]; exact v4'.1)
        show S2.mem.readLE pp 32 = _
        rw [hv]
        exact v3
      · simp only [outside_cons, outside_nil, and_true]
        omega
  · rw [hF.accessible]; exact hE1
  · simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
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
  · rw [hF.accessible]; exact hB1
  · simp only [outside_cons, outside_nil, and_true] at hB2 ⊢
    omega
  · obtain ⟨b1, b2⟩ := hzbuf
    exact ⟨by rw [hF.accessible]; exact b1, b2⟩
  · exact hWinZ
  · rcases hzR with h | h
    · exact Or.inl h
    · exact Or.inr (InRanges.of_subset h hL)
  · exact hzP
  · exact hzS
  · rw [hr28]; exact hzg
  · exact hstrH.get.2
  · exact hstrH.get.1
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
      · exact Janus.Arm64.Memory.accessible_sub S2.mem h0 (Or.inl rfl) h1 (by omega)
    · rcases hsR' with h | h
      · exact Or.inl (Outside.of_sub h h1 (by omega))
      · exact Or.inr (InRanges.sub h h1 (by omega))
    · exact Outside.of_sub hsP' h1 (by omega)


/-- the facts about the state `S2` after `string(b)` (the live `slicebytetostring` contract, buffer `sp - 40`), in the form the
engine leaves them -/
theorem byt_call_pre {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI r0 r1 : BitVec 64} {s S1 S2 : State}
    (hpre : PreB C sb st R R2 T b L lo hi z pI nI s) (hlo : lo + 4720 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hF1 : MemFrame s.mem S1.mem [(lo, hi)])
    (hmf : MemFrame S1.mem S2.mem (R.rt ++ [(s.sp.toNat - 80 - 4096, s.sp.toNat - 80 - 8),
      (s.sp.toNat - 80 + 8, s.sp.toNat - 80 + 8 + 24)] ++
      if s.sp.toNat - 40 = 0 then [] else [(s.sp.toNat - 40, s.sp.toNat - 40 + 32)]))
    (hsoa : (r1.toNat = (strBytes S1.mem pI.toNat nI.toNat).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
        (0 < r1.toNat → s.mem.accessible r0.toNat r1.toNat false = true) ∧
        strBytes S2.mem r0.toNat r1.toNat = strBytes S1.mem pI.toNat nI.toNat) ∧
      StrAt R.rt (s.sp.toNat - 40) st pI.toNat r1.toNat r0.toNat S1.mem)
    (hlf : LiveFrame S1.mem S2.mem L (if s.sp.toNat - 40 = 0 then [] else [(s.sp.toNat - 40, s.sp.toNat - 40 + 32)]))
    (hfr : FreshFrom (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L)
    (hinv : R.inv (b - roundupsize nI.toNat true)
      (L ++ ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (s.regs 28).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) S2.mem))
    (hr0 : S2.regs 0 = z) (hr1 : S2.regs 1 = r0) (hr2 : S2.regs 2 = r1) (hsp2 : S2.sp = s.sp - 80#64)
    (hr28 : S2.regs 28 = s.regs 28) :
    TopPre0 C R R2 T (b - roundupsize nI.toNat true) (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]))
      lo (s.sp.toNat - 40) z r0 nI S2 ∧
    (∀ k, k < nI.toNat → S2.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1) ∧
    MemFrame s.mem S2.mem (R.rt ++ [(lo, hi)]) := by
  obtain ⟨hSO, hSA⟩ := hsoa
  have hpre' := hpre
  obtain ⟨hMod, hEnv, hok, hcost, hstW, hstR, hstP, hstZ, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo, hMr, hMb,
    hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hRW, hchunk⟩ := hpre'
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hbne : s.sp.toNat - 40 ≠ 0 := by omega
  rw [if_neg hbne] at hmf hlf
  have hn : r1.toNat = nI.toNat := by rw [hSO.1]; simp
  have hr2' : S2.regs 2 = nI := by rw [hr2]; exact BitVec.eq_of_toNat_eq hn
  have hF : MemFrame s.mem S2.mem (R.rt ++ [(lo, hi)]) := by
    refine hF1.trans hmf (fun a n h => ?_)
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨h2, ⟨⟨h1, by omega, by omega⟩, by omega⟩⟩
  have hadds : ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])) =
      (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]) := by
    rw [adds_eq, hn]
  rw [hadds] at hinv
  rw [hn] at hSO hSA
  have hr28n : (S2.regs 28).toNat = (s.regs 28).toNat := by rw [hr28]
  have hMod' := hMod
  obtain ⟨-, -, -, -, -, hLpriv, -⟩ := hMod'
  have hstW' : Outside st 2048 [(lo, hi)] := hstW
  have hprt : ∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt := hMod.2.2.2.2.1
  have hpwf : ∀ r ∈ R2.priv, r.1 ≤ r.2 := hInit.2.2.2.2
  by_cases hz0 : nI.toNat = 0
  · rw [if_pos hz0] at hinv ⊢
    refine ⟨?_, fun k hk => absurd hk (by omega), hF⟩
    refine byt_top0 C hpre hlo hhi (hi3 := s.sp.toNat - 40) (Nat.le_refl _) (by omega) hr0 hr1 hr2' hsp2 hr28 hF
      (L' := L ++ []) (fun r hr => List.mem_append_left _ hr) ?_ ?_ ⟨by have := hSO.2.1; omega, Or.inl hz0⟩
      (Or.inl hz0) (Or.inl hz0) (Or.inl hz0) (Or.inl hz0) rfl (by rw [hr28n]; exact hinv)
    · intro r hr
      have h := e18 r (by simpa using hr)
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega
    · intro r hr
      exact hLpriv r (by simpa using hr)
  · have hpos : 0 < nI.toNat := Nat.pos_of_ne_zero hz0
    have hfr' : 32 < nI.toNat → ApartAll r0.toNat nI.toNat L := by
      intro h32
      have := hfr
      rw [hn] at this
      rw [if_pos (by omega), if_neg hz0] at this
      simpa using this _ (List.mem_singleton_self _)
    obtain ⟨hlw, hlp, hlz⟩ := loc (hi3 := s.sp.toNat - 40) hSA hpos (by omega) (by omega)
      (Nat.le_refl _) (by omega) e9 e10 hpwf hprt hstW' hstP hstZ hzwin hzR hbne hfr'
    rw [if_neg hz0] at hinv ⊢
    have hbytes : ∀ k, k < nI.toNat → S2.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1 := by
      intro k hk
      have hq := congrArg (fun l => l.getD k 0) hSO.2.2.2
      rw [strBytes_getD _ _ _ _ (by omega), strBytes_getD _ _ _ _ (by omega)] at hq
      have e := hF1.readLE (pI.toNat + k) 1 (by
        have := hiwin
        simp only [outside_cons, outside_nil, and_true]; omega)
      rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at e
      rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one, hq, e]
    refine ⟨?_, hbytes, hF⟩
    have hlw2 : r0.toNat + nI.toNat ≤ lo ∨ s.sp.toNat - 40 ≤ r0.toNat := by
      have h := hlw
      simp only [outside_cons, outside_nil, and_true] at h
      exact h
    refine byt_top0 C hpre hlo hhi (hi3 := s.sp.toNat - 40) (Nat.le_refl _) (by omega) hr0 hr1 hr2' hsp2 hr28 hF
      (L' := L ++ [(r0.toNat, r0.toNat + nI.toNat)]) (fun r hr => List.mem_append_left _ hr) ?_ ?_
      ⟨by have := hSO.2.1; omega, Or.inr (by rw [hF.accessible]; exact hSO.2.2.1 hpos)⟩
      (Or.inr hlw2) (Or.inr hlz) ?_ (Or.inr hlp) rfl (by rw [hr28n]; exact hinv)
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
      · exact hLpriv r h
      · simp only [List.mem_singleton] at h
        subst h
        rw [Nat.add_sub_cancel_left]; exact hlp
    · exact Or.inr (Or.inr ⟨(r0.toNat, r0.toNat + nI.toNat), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)

end Fv256.Arm64.ScanByt0
