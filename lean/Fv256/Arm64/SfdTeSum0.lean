import Fv256.Arm64.SfdTePre
import Fv256.Arm64.SfdTeTail0
import Fv256.Arm64.SfdTeObj0

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

/-- `omega` after dropping the hypotheses unrelated to the goal (the contexts carry giant memory terms) -/
theorem rr_mono {p : Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', a, b, c⟩ := h
  exact ⟨k, s', a, b, hQ _ c⟩

macro "te_omega" : tactic => `(tactic| first | (janus_clear_irrel; omega) | omega)

theorem reach_name {p : Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_sum0 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Contracts.Iface.Ifaceeq (P.link impl) (P.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (P.link impl) (P.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (P.link impl) (P.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (P.link impl) (P.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (P.link impl) te (fun s => TePre R R2 T b L fp fl sp sl s ∧ s.mem.readLE wbFlag 4 = 0)
      (TePost R R2 b L fp fl sp sl) := by
  intro s hpc ⟨⟨hl1, hl2, h0, h1, h2, h3, h6, h7, hsl1, hsl2, hlow, ⟨_, hdep8, hdep, hTty, hprR, hLpr, hrt0, hsR, hsP, hokn, hok1, hok2⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩,
    ⟨hokm, hokv, hbud, hsacc, hsp48, hsdisj, hspR, hspP⟩⟩, hfl⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := e15
  have hsp0 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by rw [BitVec.toNat_sub]; simp; te_omega
  have hcOK : Iface.CallerOK R2 s 96 72 := by
    refine ⟨e16, ⟨by simp only [regG, stackguard0Offset]; omega, by simp only [regG, stackguard0Offset]; exact e7, by
      simp only [stackguard0, regG, stackguard0Offset]; omega⟩, e4, hdep8, by omega, by omega, ?_, ?_, ?_, e12⟩
    · exact Memory.accessible_mono _ e5 (by te_omega) (by te_omega)
    · exact Outside.of_sub e10 (by te_omega) (by te_omega)
    · simp only [Spec.Disjoint]; te_omega
  janus_run until [P.contractAddr "runtime.ifaceeq"]
  refine reach_name ?_
  intro S hS
  have hS4 : S.sp.toNat = s.sp.toNat - 96 := by subst hS; exact hsp0
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (R2.depth + 96), s.sp.toNat + 72)] := by
    subst hS
    dsimp only
    janus_frame
  have hpre0 : Iface.RTPre R2 3 S := Iface.RTPre.of_caller hl hcOK hSf hS4 (by subst hS; rfl) (by subst hS; simp [setReg_apply])
    (by subst hS; simp [setReg_apply]) (by te_omega) (by te_omega)
  have hSacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := hSf.accessible
  have hSreg : S.regs 0 = BitVec.ofNat 64 errItab ∧ S.regs 1 = BitVec.ofNat 64 synConst ∧
      S.regs 2 = BitVec.ofNat 64 synConst := by
    subst hS; simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; decide
  have oI := e14 (errItab, errItab + 16) (by simp [staticRanges])
  have oS := e14 (synConst, synConst + 8) (by simp [staticRanges])
  have oE := e14 (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
  have oW := e14 (wbFlag, wbFlag + 4) (by simp [staticRanges])
  have oN := e14 (numErrType, numErrType + 16) (by simp [staticRanges])
  simp only [Nat.add_sub_cancel_left] at oI oS oE oW oN
  obtain ⟨-, -, -, -, -, -, -, hout2, -, -⟩ := hcOK
  have hdesc := hl.type_desc S.mem (S.regs 28) T hpre0.1 hTty
  have hTw : Outside T 48 [(s.sp.toNat - (R2.depth + 96), s.sp.toNat + 72)] := by
    have := InRanges.disjoint hdesc.2.2.2 hout2
    simp only [typeDescSize] at this
    simp only [outside_cons, outside_nil, and_true]
    omega
  have hWsub : ∀ a n, Outside a n [(s.sp.toNat - 4192, s.sp.toNat + 72)] →
      Outside a n [(s.sp.toNat - (R2.depth + 96), s.sp.toNat + 72)] := by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  have hTS : S.mem.readLE (errItab + 8) 8 = T := by
    rw [hSf.readLE _ _ (hWsub _ _ (Outside.of_sub oI (by te_omega) (by te_omega)))]; exact t1
  have hregS : isRegularMemory S.mem T = true := by
    simp only [isRegularMemory, tyTFlag] at t3 ⊢
    rw [hSf.readLE _ _ (Outside.of_sub hTw (by te_omega) (by te_omega))]; exact t3
  have hndS : isDirectIface S.mem T = false := by
    simp only [isDirectIface, tyTFlag] at t4 ⊢
    rw [hSf.readLE _ _ (Outside.of_sub hTw (by te_omega) (by te_omega))]; exact t4
  have hszS : tySize S.mem T = 8 := by
    simp only [tySize] at t5 ⊢
    rw [hSf.readLE _ _ (Outside.of_sub hTw (by te_omega) (by te_omega))]; exact t5
  have hxacc : S.mem.accessible synConst (tySize S.mem T) false = true := by
    rw [hszS, hSacc]; exact t11
  have hcmp := (hl.regular S.mem (S.regs 28) T synConst synConst hpre0.1 hTty hregS hndS hxacc hxacc)
  have hS0 : (S.regs 0).toNat = errItab := by
    rw [hSreg.1]; simp only [BitVec.toNat_ofNat]; decide
  refine ReachesRet.call hif (by subst hS; rfl) ⟨hpre0, fun _ => ⟨by rw [hS0]; decide, ?_, ?_, ?_⟩⟩ ?_
  · rw [hS0, hSacc]; exact t10
  · rw [hS0, hTS]; exact hdesc.1
  · have h1 : (S.regs 1).toNat = synConst := by rw [hSreg.2.1]; simp only [BitVec.toNat_ofNat]; decide
    have h3 : (S.regs 2).toNat = synConst := by rw [hSreg.2.2]; simp only [BitVec.toNat_ofNat]; decide
    rw [hS0, hTS, h1, h3]
    exact fun _ => ⟨hTty, hcmp.1⟩
  · intro s' hpc' ⟨r, x, fl0, m', hs', hfr, henv', hres⟩
    have h1 : (S.regs 1).toNat = synConst := by rw [hSreg.2.1]; simp only [BitVec.toNat_ofNat]; decide
    have h3 : (S.regs 2).toNat = synConst := by rw [hSreg.2.2]; simp only [BitVec.toNat_ofNat]; decide
    have hres' : (r 0).toNat % 256 = 1 := by
      rw [hres]
      have hT0 : T ≠ 0 := hdesc.1
      simp only [Janus.Contracts.Iface.ifaceEqual, Janus.Contracts.Iface.efaceEqual, hS0, hTS, h1, h3, hndS]
      have := hcmp.2
      rw [hszS] at this
      simp [hT0, this]
    have hinvS : R.inv b L (s.regs 28).toNat (view R.rt L S.mem) :=
      RtInv.inv_frame hSf (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact Outside.of_sub e9 (by te_omega) (by te_omega)) e17
    have hfr' := hfr
    simp only [Iface.rtWrites, calleeStack, List.append_nil, hS4] at hfr'
    have hgm : m'.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
      rw [hfr'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨e12, ?_, ?_⟩ <;> simp only [Spec.Disjoint] at * <;> omega)]
      exact hSf.readLE _ _ (by
        simp only [outside_cons, outside_nil, and_true]
        omega)
    have hinv' : R.inv b L (s.regs 28).toNat (view R.rt L m') :=
      RtInv.inv_frame' hfr' (by
        intro r hr
        left
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with hr | hr | hr
        · exact hprR r hr
        · subst hr; exact Outside.of_sub e9 (by te_omega) (by te_omega)
        · subst hr; exact Outside.of_sub e9 (by te_omega) (by te_omega)) hinvS
    have hS30 : S.regs 30 = 618732#64 := by subst hS; simp [setReg_apply]
    have hkey : ∀ a v, S.mem.readLE a 8 = v → s.sp.toNat + 8 ≤ a → a + 8 ≤ s.sp.toNat + 72 → m'.readLE a 8 = v := by
      intro a v hv h1 h2
      rw [hfr'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨Outside.of_sub e10 (by te_omega) (by te_omega), by omega, by omega⟩)]
      exact hv
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hSlr : S.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      subst hS; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt (s.regs 30).isLt
    have hSfp : S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
      subst hS; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
    have hof30 : BitVec.ofNat 64 (s.regs 30).toNat = s.regs 30 := by simp
    have hof29 : BitVec.ofNat 64 (s.regs 29).toNat = s.regs 29 := by simp
    have hSm8 : S.mem.readLE (s.sp.toNat + 8) 8 = fp.toNat := by
      subst hS; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt fp.isLt
    have hSm16 : S.mem.readLE (s.sp.toNat + 16) 8 = fl.toNat := by
      subst hS; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt fl.isLt
    have hSm24 : S.mem.readLE (s.sp.toNat + 24) 8 = sp.toNat := by
      subst hS; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt sp.isLt
    have hSm32 : S.mem.readLE (s.sp.toNat + 32) 8 = sl.toNat := by
      subst hS; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt sl.isLt
    have hsl32 : m'.readLE (s.sp.toNat + 32) 8 = sl.toNat := hkey _ _ hSm32 (by te_omega) (by te_omega)
    have hrsp : S.sp = s.sp - 96#64 := by subst hS; rfl
    have hg28 : S.regs 28 = s.regs 28 := by subst hS; simp [setReg_apply]
    have hgm2 : m'.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 96 := by rw [hgm]; te_omega
    have hLw : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 96 - 4096 ∨ s.sp.toNat - 96 - 8 ≤ r.1) ∧
        (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 96 + 8 ∨ s.sp.toNat - 96 + 8 + 24 ≤ r.1) := by
      intro r hr
      have := e18 r hr
      simp only [outside_cons, outside_nil, and_true] at this
      omega
    have hsl24 : m'.readLE (s.sp.toNat + 24) 8 = sp.toNat := hkey _ _ hSm24 (by te_omega) (by te_omega)
    have hbL : blockSize sl.toNat true ≤ b := by te_omega
    have hg6 : (s.regs 28).toNat ≤ 281474976710632 := by te_omega
    have hga1 : (s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 96 - 4096 ∨ s.sp.toNat - 96 - 8 ≤ (s.regs 28).toNat + 16 := by te_omega
    have hga2 : (s.regs 28).toNat + 16 ≤ s.sp.toNat - 96 ∨ s.sp.toNat - 96 + 16 ≤ (s.regs 28).toNat := by te_omega
    have hbit : (BitVec.getLsbD (r 0) 0 == false) = false := by
      have h1 : (r 0).getLsbD 0 = true := by
        simp [BitVec.getLsbD, Nat.testBit_zero]
        omega
      simp [h1]
    subst hs'
    janus_run [hrsp, hS30, hbit, hsl32, hg28] until [P.contractAddr "runtime.mallocgc"]
    janus_run [hrsp, hS30, hbit, hsl32, hSm24, hSm32, hSm8, hSm16, hg28, hokv] until [P.contractAddr "runtime.memmove"] calls [hmg.pos]
    rename BitVec 64 => q
    rename Memory => m2
    rename LiveFrame _ _ _ _ => hLF1
    rename MemFrame m' _ _ => hMF1
    rename ApartAll _ _ L => hApL
    rename InRanges _ (blockSize sl.toNat true) R.rt => hInR
    rename _ + blockSize sl.toNat true ≤ 281474976710656 => hq48
    have hqpos : 0 < q.toNat := by
      obtain ⟨r, hr, h1, h2⟩ := hInR
      have := hrt0 r hr
      omega
    have hnp : ¬(18446744073709551616 - q.toNat) % 18446744073709551616 < sl.toNat := by
      have : sl.toNat ≤ blockSize sl.toNat true := by assumption
      omega
    janus_run [hrsp, hS30, hbit, hsl32, hSm24, hSm32, hSm8, hSm16, hg28, hokv, hnp] until [P.contractAddr "runtime.newobject"] calls [hmv]
    rename Memory => m3
    rename MemFrame _ m3 _ => hMF2
    have pN := hsR (numErrType, numErrType + 16) (by simp [staticRanges])
    have qN := hsP (numErrType, numErrType + 16) (by simp [staticRanges])
    simp only [Nat.add_sub_cancel_left] at pN qN
    have hM3 : ∀ a n, Outside a n R.rt → Outside a n R2.priv → Outside a n [(s.sp.toNat - 4192, s.sp.toNat + 72)] →
        Outside a n [(q.toNat, q.toNat + sl.toNat)] → m3.readLE a n = s.mem.readLE a n := by
      intro a n h1 h2 h3 h4
      simp only [outside_cons, outside_nil, and_true] at h3 h4
      rw [hMF2.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h1 | omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by te_omega),
          hMF1.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h1 | omega),
          hfr'.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h2 | omega)]
      exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hqN : Outside numErrType 16 [(q.toNat, q.toNat + sl.toNat)] := by
      have := InRanges.disjoint hInR pN
      simp only [outside_cons, outside_nil, and_true]; te_omega
    have oN8 : Outside numErrType 8 R.rt := Outside.of_sub pN (by te_omega) (by te_omega)
    have hN0 : m3.readLE numErrType 8 = 48 := by
      rw [hM3 numErrType 8 oN8 (Outside.of_sub qN (by te_omega) (by te_omega)) (Outside.of_sub oN (by te_omega) (by te_omega))
        (Outside.of_sub hqN (by te_omega) (by te_omega))]; exact t6
    have hN1 : m3.readLE (numErrType + 8) 8 ≠ 0 := by
      rw [hM3 (numErrType + 8) 8 (Outside.of_sub pN (by te_omega) (by te_omega)) (Outside.of_sub qN (by te_omega) (by te_omega))
        (Outside.of_sub oN (by te_omega) (by te_omega)) (Outside.of_sub hqN (by te_omega) (by te_omega))]; exact t7
    have hN1b : (m3.readLE (numErrType + 8) 8 == 0) = false := by simp [hN1]
    have hb48 : 48 ≤ b - blockSize sl.toNat true := by
      have : blockSize 48 false = 48 := by decide
      omega
    have hoNd := oN
    simp only [outside_cons, outside_nil, and_true] at hoNd
    janus_run [hrsp, hS30, hbit, hsl32, hSm24, hSm32, hSm8, hSm16, hg28, hokv, hnp, hfl, hN0, hN1b, hb48, hoNd, hSlr, hSfp, hof30, hof29] until [te + 0xd8] calls [hnew.pos]
    rename BitVec 64 => t
    rename Memory => m4
    rename MemFrame _ m4 _ => hMF3
    rename InRanges _ (blockSize 48 false) R.rt => hInT
    rename s.mem.accessible (BitVec.toNat t) 48 true = true => hTacc
    have pW := hsR (wbFlag, wbFlag + 4) (by simp [staticRanges])
    have qW := hsP (wbFlag, wbFlag + 4) (by simp [staticRanges])
    simp only [Nat.add_sub_cancel_left] at pW qW
    have hqW : Outside wbFlag 4 [(q.toNat, q.toNat + sl.toNat)] := by
      have := InRanges.disjoint hInR pW
      simp only [outside_cons, outside_nil, and_true]; te_omega
    have hf3 : m3.readLE wbFlag 4 = 0 := by
      rw [hM3 wbFlag 4 pW qW (by simp only [outside_cons, outside_nil, and_true] at oW ⊢; omega) hqW]; exact hfl
    have hoWd := oW
    simp only [outside_cons, outside_nil, and_true] at hoWd
    have hf4 : m4.readLE wbFlag 4 = 0 := by
      rw [hMF3.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact pW | omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by te_omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by te_omega)]
      exact hf3
    have hInTW := InRanges.disjoint hInT pW
    have hacc4 : m4.accessible wbFlag 4 false = true := by
      rw [hMF3.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF2.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF1.accessible, hfr'.accessible, hSf.accessible]
      exact t8
    have hacc4t : m4.accessible t.toNat 48 true = true := by
      rw [hMF3.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF2.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF1.accessible, hfr'.accessible, hSf.accessible]
      exact hTacc
    have hacc4e : m4.accessible strconvErrSyntax 16 false = true := by
      rw [hMF3.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF2.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF1.accessible, hfr'.accessible, hSf.accessible]
      exact t9
    have hacc4w : m4.accessible (BitVec.toNat s.sp - 4192) (BitVec.toNat s.sp + 72 - (BitVec.toNat s.sp - 4192)) true = true := by
      rw [hMF3.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF2.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF1.accessible, hfr'.accessible, hSf.accessible]
      exact e5
    have hf4b : (m4.readLE wbFlag 4 == 0) = true := by simp [hf4]
    rename BitVec.toNat t ≤ 281474976710608 => ht48'
    rename sl.toNat ≤ blockSize sl.toNat true => hQsl
    rename ApartAll (BitVec.toNat t) 48 L ∧ Apart (BitVec.toNat t) 48 (BitVec.toNat q) (blockSize sl.toNat true) => hApT
    rename LiveFrame _ m4 _ _ => hLF3
    rename Mem.Copied _ m3 _ _ _ => hCop
    rename R.1 _ _ _ (view R.rt _ m4) => hinvN
    have pE := hsR (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
    have qE := hsP (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
    simp only [Nat.add_sub_cancel_left] at pE qE
    have hg18 : S.regs 18 = s.regs 18 := by subst hS; simp [setReg_apply]
    have hlrS : ∀ a n, Outside a n R.rt → Outside a n R2.priv →
        (a + n ≤ s.sp.toNat - 96 - 4096 ∨ s.sp.toNat - 96 - 8 ≤ a) → (a + n ≤ s.sp.toNat - 96 + 8 ∨ s.sp.toNat - 96 + 8 + 24 ≤ a) →
        (a + n ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 32 ≤ a) → (a + n ≤ s.sp.toNat - 24 ∨ s.sp.toNat - 16 ≤ a) →
        (a + n ≤ s.sp.toNat - 16 ∨ s.sp.toNat - 8 ≤ a) → m4.readLE a n = S.mem.readLE a n := by
      intro a n h1 h2 d1 d2 d3 d4 d5
      have hq := InRanges.disjoint hInR h1
      rw [hMF3.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h1 | omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          hMF2.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h1 | omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          hMF1.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h1 | omega),
          hfr'.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact h2 | omega)]
    have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat + 72 → Outside a n R.rt ∧ Outside a n R2.priv :=
      fun a n h1 h2 => ⟨Outside.of_sub e9 (by te_omega) (by te_omega), Outside.of_sub e10 (by te_omega) (by te_omega)⟩
    have hlr4 : m4.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      rw [hlrS _ _ (hwin _ _ (by te_omega) (by te_omega)).1 (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega)
        (by te_omega) (by te_omega) (by te_omega), ← hSlr]
    have hfp4 : m4.readLE (s.sp.toNat - 96 - 8) 8 = (s.regs 29).toNat := by
      rw [hlrS _ _ (hwin _ _ (by te_omega) (by te_omega)).1 (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega)
        (by te_omega) (by te_omega) (by te_omega)]
      have : s.sp.toNat - 96 - 8 = s.sp.toNat - 104 := by omega
      rw [this]; exact hSfp
    have hts4 := InRanges.disjoint hInT e9
    have hte4 := InRanges.disjoint hInT pE
    have hwF : wbFlag + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ wbFlag := hInTW
    janus_run [hrsp, hS30, hbit, hsl32, hSm24, hSm32, hSm8, hSm16, hg28, hf4, hacc4, hacc4w, hacc4t, hacc4e, hSlr, hSfp, hof30, hof29] until [te + 0xe0]
    refine rr_mono (te_tail0 impl _ m4 fl.toNat t (s.regs 30) (s.regs 29) rfl rfl (by simp [callRegs, setReg_apply])
      (by show m4.readLE (s.sp - 96#64).toNat 8 = _; rw [hsp0]; exact hlr4) (by simpa using hl1)
      (by simp at hl2 ⊢; omega)
      (by show m4.readLE ((s.sp - 96#64).toNat - 8) 8 = _; rw [hsp0]; exact hfp4)
      (by show (s.sp - 96#64).toNat % 16 = 0; rw [hsp0]; te_omega)
      (by show 4096 ≤ (s.sp - 96#64).toNat; rw [hsp0]; te_omega)
      (by show (s.sp - 96#64).toNat + 168 ≤ 2 ^ 48; rw [hsp0]; te_omega)
      (by show m4.accessible ((s.sp - 96#64).toNat - 4096) (4096 + 168) true = true; rw [hsp0]
          exact Memory.accessible_mono _ hacc4w (by te_omega) (by te_omega))
      (by te_omega) hacc4t hacc4e hacc4 hf4
      (by show t.toNat + 48 ≤ (s.sp - 96#64).toNat - 4096 ∨ (s.sp - 96#64).toNat + 168 ≤ t.toNat; rw [hsp0]; te_omega)
      (by te_omega) hwF) ?_
    -- the finished object
    intro s' ⟨hsp', hr0, hr1, hr29, hr28, hr18, hmem'⟩
    simp only [] at hmem' hsp' hr28 hr18
    rw [hsp0] at hmem'
    have b48 : blockSize 48 false = 48 := by decide
    have qlt : q.toNat < 2 ^ 64 := q.isLt
    have hq4 : m4.readLE (s.sp.toNat - 24) 8 = q.toNat := by
      rw [hMF3.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact (hwin _ _ (by te_omega) (by te_omega)).1 | te_omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt qlt
    have hsl4 : m4.readLE (s.sp.toNat - 40) 8 = sl.toNat := by
      rw [hMF3.readLE _ _ (by
            simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
            (repeat' apply And.intro) <;> first | exact (hwin _ _ (by te_omega) (by te_omega)).1 | te_omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt sl.isLt
    have hfn4 : m4.readLE (s.sp.toNat + 8) 8 = fp.toNat := by
      rw [hlrS _ _ (hwin _ _ (by te_omega) (by te_omega)).1 (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega)
        (by te_omega) (by te_omega) (by te_omega)]
      exact hSm8
    have he0 : ∀ a, (a = strconvErrSyntax ∨ a = strconvErrSyntax + 8) → m4.readLE a 8 = s.mem.readLE a 8 := by
      intro a ha
      have hao : Outside a 8 [(s.sp.toNat - 4192, s.sp.toNat + 72)] := by
        rcases ha with rfl | rfl
        · exact Outside.of_sub oE (by te_omega) (by te_omega)
        · exact Outside.of_sub oE (by te_omega) (by te_omega)
      have hap : Outside a 8 R.rt := by
        rcases ha with rfl | rfl
        · exact Outside.of_sub pE (by te_omega) (by te_omega)
        · exact Outside.of_sub pE (by te_omega) (by te_omega)
      have hapr : Outside a 8 R2.priv := by
        rcases ha with rfl | rfl
        · exact Outside.of_sub qE (by te_omega) (by te_omega)
        · exact Outside.of_sub qE (by te_omega) (by te_omega)
      simp only [outside_cons, outside_nil, and_true] at hao
      rw [hlrS _ _ hap hapr (by te_omega) (by te_omega) (by te_omega) (by te_omega) (by te_omega)]
      exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
    have e0lt : s.mem.readLE strconvErrSyntax 8 < 2 ^ 64 := by
      have := Janus.Arm64.Memory.readLE_lt s.mem strconvErrSyntax 8
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl] at this; exact this
    have e1lt : s.mem.readLE (strconvErrSyntax + 8) 8 < 2 ^ 64 := by
      have := Janus.Arm64.Memory.readLE_lt s.mem (strconvErrSyntax + 8) 8
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl] at this; exact this
    have a72 : s.sp.toNat - 96 + 72 = s.sp.toNat - 24 := by omega
    have a56 : s.sp.toNat - 96 + 56 = s.sp.toNat - 40 := by omega
    have a104 : s.sp.toNat - 96 + 104 = s.sp.toNat + 8 := by omega
    rw [a72, a56, a104, hq4, hsl4, hfn4, he0 _ (Or.inl rfl), he0 _ (Or.inr rfl)] at hmem'
    have hf := tm_fields m4 t.toNat fl.toNat q.toNat sl.toNat (s.mem.readLE strconvErrSyntax 8)
      (s.mem.readLE (strconvErrSyntax + 8) 8) fp.toNat fl.isLt qlt sl.isLt e0lt e1lt fp.isLt
    have hbase := te0_base hSf hfr' hMF1 hMF2 hMF3 hdep hlow hInR hQsl
    have hFin : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) := by
      rw [hmem']; exact tm_frame hbase (fun r hr => by simp [hr]) hInT
    refine ⟨?_, hr29, ?_, ?_, ⟨q.toNat, t, hr0, hr1, ?_⟩, hFin⟩
    · rw [hsp']; show s.sp - 96#64 + 96#64 = s.sp; bv_omega
    · rw [hr28]; simp [callRegs, setReg_apply, Map.keepABI, hg28]
    · rw [hr18]; simp [callRegs, setReg_apply, Map.keepABI, hg18]
    · unfold TeObj
      rw [hmem']
      refine ⟨hInR, hInT, hApL, ?_, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, ?_, ?_⟩
      · simp only [apartAll_append, apartAll_cons, apartAll_nil, and_true, b48, Nat.add_sub_cancel_left]; exact hApT
      · intro k hk
        have hqw := InRanges.disjoint hInR e9
        have hApt := hApT.2
        simp only [Apart] at hqw hApt
        have hsrc : (m2.writeLE (s.sp.toNat - 16) 8 q.toNat).readLE (sp.toNat + k) 1 = s.mem.readLE (sp.toNat + k) 1 := by
          rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by te_omega)]
          rcases hspR with ho | hi
          · rw [hMF1.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              refine ⟨Outside.of_sub ho (by te_omega) (by te_omega), ?_, ?_⟩ <;> te_omega)]
            rw [hfr'.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              refine ⟨Outside.of_sub hspP (by te_omega) (by te_omega), ?_, ?_⟩ <;> te_omega)]
            exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
          · rw [hLF1.readLE_nil _ _ (InRanges.sub hi (by te_omega) (by te_omega))]
            rw [hfr'.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              refine ⟨Outside.of_sub hspP (by te_omega) (by te_omega), ?_, ?_⟩ <;> te_omega)]
            exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
        exact te0_copy (hLF := hLF3) (hApt := hApt) hk hQsl (by te_omega) (by te_omega) hCop hsrc
      · rw [tm_view (rt := R.rt) ⟨(t.toNat, t.toNat + blockSize 48 false), by simp, Nat.le_refl _, by rw [b48]⟩]
        exact hinvN

end Fv256.Arm64.SfdToError
