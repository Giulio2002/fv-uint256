import Fv256.Arm64.SfdTePre
import Fv256.Arm64.SfdTe1F

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError


theorem reach_name1 {p : Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te1_pre (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Contracts.Iface.Ifaceeq (P.link impl) (P.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (P.link impl) (P.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (P.link impl) (P.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (P.link impl) (P.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcont : ∀ (s S St : State) (m' m2 m3 m4 : Janus.Arm64.Memory) (q t : BitVec 64),
      St.pc = BitVec.ofNat 64 (te + 0xd8) → St.regs 0 = t →
      St.mem = m4.writeLE (t.toNat + 8) 8 fl.toNat → St.regs 27 = 1978368#64 → St.sp = s.sp - 96#64 →
      St.regs 28 = s.regs 28 → St.regs 18 = s.regs 18 →
      R.ok (P.contractAddr "runtime.gcWriteBarrier1") [1] → R.ok (P.contractAddr "runtime.gcWriteBarrier2") [2] →
      (s.regs 30).toNat % 4 = 0 → (s.regs 30).toNat < 2 ^ 48 →
      Pre1 R R2 b L fp fl sp sl s S m' m2 m3 m4 q t →
      ReachesRet (P.link impl) (s.regs regLR) St (TePost R R2 b L fp fl sp sl s)) :
    Summary (P.link impl) te (fun s => TePre R R2 T b L fp fl sp sl s ∧ s.mem.readLE wbFlag 4 ≠ 0)
      (TePost R R2 b L fp fl sp sl) := by
  intro s hpc ⟨⟨hl1, hl2, h0, h1, h2, h3, h6, h7, hsl1, hsl2, hlow, ⟨_, hdep8, hdep, hTty, hprR, hLpr, hrt0, hsR, hsP, hokn, hok1, hok2, hT⟩,
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
  refine reach_name1 ?_
  intro S hS
  have hS4 : S.sp.toNat = s.sp.toNat - 96 := by subst hS; exact hsp0
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (R2.depth + 96), s.sp.toNat + 72)] := by
    subst hS
    dsimp only
    janus_frame
  have hpre0 : Iface.RTPre R2 3 S := Iface.RTPre.of_caller hl hcOK hSf hS4 (by subst hS; rfl) (by subst hS; simp [setReg_apply])
    (by subst hS; simp [setReg_apply]) (by te_omega) (by te_omega)
  have hSacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := hSf.accessible
  have hSrec : S.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
      S.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 := by
    subst hS; dsimp only
    constructor <;> simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
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
    have qN := hsP (numErrType, numErrType + 16) (by simp [staticRanges]) (by intro h; simp [Prod.ext_iff] at h; omega)
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
    have qW := hsP (wbFlag, wbFlag + 4) (by simp [staticRanges]) (by intro h; simp [Prod.ext_iff] at h; omega)
    simp only [Nat.add_sub_cancel_left] at pW qW
    have hqW : Outside wbFlag 4 [(q.toNat, q.toNat + sl.toNat)] := by
      have := InRanges.disjoint hInR pW
      simp only [outside_cons, outside_nil, and_true]; te_omega
    have hf3 : m3.readLE wbFlag 4 ≠ 0 := by
      rw [hM3 wbFlag 4 pW qW (by simp only [outside_cons, outside_nil, and_true] at oW ⊢; omega) hqW]; exact hfl
    have hoWd := oW
    simp only [outside_cons, outside_nil, and_true] at hoWd
    have hf4 : m4.readLE wbFlag 4 ≠ 0 := by
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
    rename BitVec.toNat t ≤ 281474976710608 => ht48'
    rename sl.toNat ≤ blockSize sl.toNat true => hQsl
    rename ApartAll (BitVec.toNat t) 48 L ∧ Apart (BitVec.toNat t) 48 (BitVec.toNat q) (blockSize sl.toNat true) => hApT
    rename LiveFrame _ m4 _ _ => hLF3
    rename Mem.Copied _ m3 _ _ _ => hCop
    rename R.1 _ _ _ (view R.rt _ m4) => hinvN
    have pE := hsR (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
    have qE := hsP (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges]) (by intro h; simp [Prod.ext_iff] at h; omega)
    simp only [Nat.add_sub_cancel_left] at pE qE
    have hg18 : S.regs 18 = s.regs 18 := by subst hS; simp [setReg_apply]
    have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat + 72 → Outside a n R.rt ∧ Outside a n R2.priv :=
      fun a n h1 h2 => ⟨Outside.of_sub e9 (by te_omega) (by te_omega), Outside.of_sub e10 (by te_omega) (by te_omega)⟩
    have hlr4 : m4.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      rw [te0_lrS hfr' hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin _ _ (by te_omega) (by te_omega)).1
        (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega)
        (by te_omega) (by te_omega) (by te_omega), ← hSlr]
    have hfp4 : m4.readLE (s.sp.toNat - 96 - 8) 8 = (s.regs 29).toNat := by
      rw [te0_lrS hfr' hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin _ _ (by te_omega) (by te_omega)).1
        (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega)
        (by te_omega) (by te_omega) (by te_omega)]
      have : s.sp.toNat - 96 - 8 = s.sp.toNat - 104 := by omega
      rw [this]; exact hSfp
    have hts4 := InRanges.disjoint hInT e9
    have hte4 := InRanges.disjoint hInT pE
    have hwF : wbFlag + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ wbFlag := hInTW
    have hInTW' : wbFlag + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ wbFlag := hInTW
    have hf4b : (m4.readLE wbFlag 4 == 0) = false := by simp [hf4]
    have hwb : wbFlag = 1979584 := by decide
    have hes : strconvErrSyntax = 1793712 := by decide
    have hwF' : 1979584 + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ 1979584 := by rw [← hwb]; exact hInTW'
    have hte4' : 1793712 + 16 ≤ t.toNat ∨ t.toNat + 48 ≤ 1793712 := by rw [← hes]; exact hte4
    refine hcont s S _ m' m2 m3 m4 q t ?_ ?_ ?_ ?_ ?_ ?_ ?_ hok1 hok2 hl1 hl2
      { hdep, hlow, e9, e10, hSf, hfr := hfr', hMF1, hMF2, hMF3, hLF1, hLF3, hCop, hinvN, hInR, hInT, hApL, hApT, hQsl, hspR, hspP,
        hsdisj, hSm8, oE, pE, qE, hf4, hacc4, hacc4t, hacc4e, hacc4w, hlr4, hfp4, hts4, hte4, hwF, hL18 := e18, hrt0, hal := e4, hsp72 := e3, e5, pW, qW, hSrec, oW }
    · first | rfl | decide
    · simp [callRegs, setReg_apply]
    · rfl
    · simp [callRegs, setReg_apply]
    · rfl
    · simp [callRegs, setReg_apply, Map.keepABI, hg28]
    · simp [callRegs, setReg_apply, Map.keepABI, hg18]

end Fv256.Arm64.SfdToError
