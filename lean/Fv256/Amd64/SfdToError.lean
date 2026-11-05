import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64

/-!
# `strconv.toError(fn, s, base, bitSize, err)` for `err == ErrSyntax` (amd64), as a callee of `strconv.ParseUint`

`ParseUint` calls `toError("ParseUint", s, 10, 64, err)` when the internal parser fails; for a syntax failure the
result is `&NumError{Func: fn, Num: cloneString(s), Err: strconv.ErrSyntax}` (a freshly allocated object, the
string copied by `mallocgc` + `memmove`).  The runtime calls are `runtime.ifaceeq` (the comparison
`err == ErrSyntax`, interface-model contract), `runtime.mallocgc`, `runtime.memmove`, `runtime.newobject` and the
write barriers (live contracts, all threaded through one `RtInv`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I

namespace Fv256.Amd64.SfdToError

abbrev te : Nat := segAddr Extracted.program "strconv.toError"

abbrev numErrType : Nat := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
abbrev numErrItab : Nat := Extracted.dataAddr.«go:itab.*strconv.NumError,error»
abbrev errItab : Nat := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»
abbrev synConst : Nat := Extracted.dataAddr.«.rodata#9967e7a3»
abbrev strconvErrSyntax : Nat := Extracted.dataAddr.«strconv.ErrSyntax»
abbrev wbFlag : Nat := Extracted.dataAddr.«runtime.writeBarrier»


open Fv256.C in
def TePre (R : RtInv) (R2 : IfaceModel) (T : Nat) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = fp ∧ s.regs 3 = fl ∧ s.regs 1 = sp ∧ s.regs 7 = sl ∧
  s.regs 9 = BitVec.ofNat 64 errItab ∧ s.regs 10 = BitVec.ofNat 64 synConst ∧
  1 ≤ sl.toNat ∧ sl.toNat < 2 ^ 40 ∧
  StackGuardOK s 4192 ∧ StackWritable s 4192 72 ∧ (s.regs 4).toNat % 8 = 0 ∧
  Extracted.program.DataLoaded s.mem ∧
  R2.depth ≤ 4096 ∧ CallerOK R2 s 96 72 ∧
  Outside ((s.regs 4).toNat - 4192) 4264 R.rt ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)]) ∧
  blockSize sl.toNat true + blockSize 48 false ≤ b ∧
  s.mem.readLE (errItab + 8) 8 = T ∧ R2.IsType T ∧ isRegularMemory s.mem T = true ∧ isDirectIface s.mem T = false ∧
  tySize s.mem T = 8 ∧
  Outside errItab 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside synConst 8 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside strconvErrSyntax 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside wbFlag 4 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside numErrType 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  (∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ (∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv) ∧
  Outside numErrType 16 R.rt ∧ Outside wbFlag 4 R.rt ∧
  R.ok (Extracted.program.contractAddr "runtime.mallocgc") [sl.toNat, 0, 0] ∧
  R.ok (Extracted.program.contractAddr "runtime.newobject") [numErrType] ∧
  (∀ q, R.ok (Extracted.program.contractAddr "runtime.memmove") [q, sp.toNat, sl.toNat]) ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  s.mem.accessible sp.toNat sl.toNat false = true ∧ sp.toNat + sl.toNat ≤ 2 ^ 48 ∧
  (sp.toNat + sl.toNat ≤ (s.regs 4).toNat - 4192 ∨ (s.regs 4).toNat + 72 ≤ sp.toNat) ∧
  Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4192) 4264 ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
  (∀ r ∈ R.rt, 0 < r.1) ∧
  Outside numErrType 16 R2.priv ∧ Outside wbFlag 4 R2.priv ∧ Outside strconvErrSyntax 16 R2.priv ∧
  s.mem.accessible wbFlag 4 false = true ∧ s.mem.accessible strconvErrSyntax 16 false = true

theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_explore (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (Extracted.program.link impl) te (TePre R R2 T b L fp fl sp sl) (fun _ _ => True) := by
  intro s hpc ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, h7, h9, h10, hsl1, hsl2, hg, ⟨hlow, hnw, hacc⟩, hal, hd, hdep, hc2,
    hout, hinv, hLs, hbud, hTd, hTty, hTreg, hTnd, hTsz, hoI, hoS, hoE, hoW, hoN, hprR, hLpr, hnR, hwR, hokm, hokn, hokv, hokb1, hokb2, hsacc, hsp48, hsdisj, hgdis, hgR, hrt0, hnP, hwP, hePr, hwbacc, heacc⟩
  have hgl := hg.load
  have hgb := hg.below
  have hgn := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hgn hgr hacc hlow hnw hal hout
  janus64_run until [Extracted.program.contractAddr "runtime.ifaceeq"]
  refine reach_name ?_
  intro S hS
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by
    subst hS; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; rw [BitVec.toNat_sub]; simp; omega
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (R2.depth + 96), (s.regs 4).toNat + 72)] := by
    subst hS
    dsimp only
    janus_frame
  have hret0 : S.mem.readLE (S.regs 4).toNat 8 = 4771624 := by
    rw [hS4]; subst hS
    dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
  have hSra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47 := by rw [hret0]; omega
  have hpre0 := RTPre.of_caller (nargs := 3) hl hc2 hSf hS4 (by subst hS; rfl) (by subst hS; simpa using hx15) (by subst hS; simpa using hdf) hSra
    (by omega) (by omega)
  have hSacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := hSf.accessible
  have hSreg : S.regs 0 = BitVec.ofNat 64 errItab ∧ S.regs 1 = BitVec.ofNat 64 synConst ∧
      S.regs 3 = BitVec.ofNat 64 synConst := by
    subst hS; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; decide
  janus64_data hd []
  obtain ⟨henv2, hguard2, hal2, hd2, hb2, hst2, hout2, hgd2, hgo2⟩ := hc2
  have hdesc := hl.type_desc S.mem (S.regs 14) T hpre0.1 hTty
  have hTw : Outside T 48 [((s.regs 4).toNat - (R2.depth + 96), (s.regs 4).toNat + 72)] := by
    have := InRanges.disjoint hdesc.2.2.2 hout2
    simp only [typeDescSize] at this
    simp only [outside_cons, outside_nil, and_true]
    omega
  have hWsub : ∀ a n, Outside a n [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] →
      Outside a n [((s.regs 4).toNat - (R2.depth + 96), (s.regs 4).toNat + 72)] := by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  have hTS : S.mem.readLE (errItab + 8) 8 = T := by
    rw [hSf.readLE _ _ (hWsub _ _ (Outside.of_sub hoI (by omega) (by omega)))]; exact hTd
  have hregS : isRegularMemory S.mem T = true := by
    simp only [isRegularMemory, tyTFlag] at hTreg ⊢
    rw [hSf.readLE _ _ (Outside.of_sub hTw (by omega) (by omega))]; exact hTreg
  have hndS : isDirectIface S.mem T = false := by
    simp only [isDirectIface, tyTFlag] at hTnd ⊢
    rw [hSf.readLE _ _ (Outside.of_sub hTw (by omega) (by omega))]; exact hTnd
  have hszS : tySize S.mem T = 8 := by
    simp only [tySize] at hTsz ⊢
    rw [hSf.readLE _ _ (Outside.of_sub hTw (by omega) (by omega))]; exact hTsz
  have hxacc : S.mem.accessible synConst (tySize S.mem T) false = true := by
    rw [hszS, hSacc]; exact Arm64.Memory.accessible_mono _ h_data12 (by decide) (by decide)
  have hcmp := (hl.regular S.mem (S.regs 14) T synConst synConst hpre0.1 hTty hregS hndS hxacc hxacc)
  have hS0 : (S.regs 0).toNat = errItab := by
    rw [hSreg.1]; simp only [BitVec.toNat_ofNat]; decide
  refine ReachesRet.call hif (by subst hS; rfl) ⟨hpre0, fun _ => ⟨by rw [hS0]; decide, ?_, ?_, ?_⟩⟩ ?_
  · rw [hS0, hSacc]; exact Arm64.Memory.accessible_mono _ h_data16 (by decide) (by decide)
  · rw [hS0, hTS]; exact hdesc.1
  · have h1 : (S.regs 1).toNat = synConst := by rw [hSreg.2.1]; simp only [BitVec.toNat_ofNat]; decide
    have h3 : (S.regs 3).toNat = synConst := by rw [hSreg.2.2]; simp only [BitVec.toNat_ofNat]; decide
    rw [hS0, hTS, h1, h3]
    exact fun _ => ⟨hTty, hcmp.1⟩
  · intro s' hpc' ⟨r, x, y, flI, m', zh, kr, hs', hfr, henv', hres⟩
    have h1 : (S.regs 1).toNat = synConst := by rw [hSreg.2.1]; simp only [BitVec.toNat_ofNat]; decide
    have h3 : (S.regs 3).toNat = synConst := by rw [hSreg.2.2]; simp only [BitVec.toNat_ofNat]; decide
    have hres' : (r 0).toNat % 256 = 1 := by
      rw [hres]
      have hT0 : T ≠ 0 := hdesc.1
      simp only [Janus.Contracts.Iface.ifaceEqual, Janus.Contracts.Iface.efaceEqual, hS0, hTS, h1, h3, hndS]
      have := hcmp.2
      rw [hszS] at this
      simp [hT0, this]
    subst hs'
    have hinvS : R.inv b L (s.regs 14).toNat (view R.rt L S.mem) :=
      RtInv.inv_frame hSf (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact Outside.of_sub hout (by omega) (by omega)) hinv
    have hfr' := hfr
    simp only [Janus.Contracts.IfaceAmd64.rtWrites, Janus.Contracts.MapAmd64.calleeStack, List.append_nil, hS4] at hfr'
    have hgm : m'.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      rw [hfr'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgo2, ?_, ?_⟩ <;> simp only [Spec.Disjoint] at hgdis <;> omega)]
      exact hSf.readLE _ _ (by
        simp only [outside_cons, outside_nil, and_true]
        simp only [Spec.Disjoint] at hgdis; omega)
    have hinv' : R.inv b L (s.regs 14).toNat (view R.rt L m') :=
      RtInv.inv_frame' hfr' (by
        intro r hr
        left
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with hr | hr | hr
        · exact hprR r hr
        · subst hr; exact Outside.of_sub hout (by omega) (by omega)
        · subst hr; exact Outside.of_sub hout (by omega) (by omega)) hinvS
    have hal : ¬ (BitVec.setWidth 8 (r 0) = 0#8) := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this
      omega
    have hal1 : BitVec.setWidth 8 (r 0) = 1#8 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    have hra' : retAddrOf S = BitVec.ofNat 64 4771624 := by simp only [retAddrOf, hret0]
    rw [hra']
    subst hS
    simp only [Janus.Contracts.IfaceAmd64.rtWrites, Janus.Contracts.MapAmd64.calleeStack, setRegF_apply, reduceIte,
      Nat.reduceEqDiff, List.append_nil] at hfr
    have hs496 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
      rw [BitVec.toNat_sub]; simp; omega
    rw [hs496] at hfr
    simp only [Spec.Disjoint] at hgdis
    clear hres hpc' hpre0 hcmp hdesc hxacc hres' hfr' hinvS hSf hSreg hSacc hS4 hret0 hSra hra' hS0 henv' h1 h3
    janus64_run [hal1, hgm] until [Extracted.program.contractAddr "runtime.memmove"] calls [hmg.pos]
    rename_i q j2 f2 x2 y2 m2 z2 k2 hLF hMF hApA hInR hQ48 hQacc hQa8 hQa16 hQz hQsl hAp hInv2 hAw hAn hAwb
    try clear hTS hregS hndS hszS
    have hrsp : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := hs496
    have hgm2 : m2.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgR, ?_, ?_⟩ <;> omega)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hgm
    have hrd : ∀ a n, Outside a n R.rt → Outside a n R2.priv →
        Outside a n [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] →
        ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE a n
          = s.mem.readLE a n := by
      intro a n h1 h2 h3
      simp only [outside_cons, outside_nil, and_true] at h3
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hMF.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h1, by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h2, by omega, by omega⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hs8 : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat + 8) 8 = fp.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout2 (by omega) (by omega), by omega, by omega⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e]; exact Nat.mod_eq_of_lt fp.isLt
    have hs16 : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat + 16) 8 = fl.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout2 (by omega) (by omega), by omega, by omega⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e]; exact Nat.mod_eq_of_lt fl.isLt
    have hs24 : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat + 24) 8 = sp.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout2 (by omega) (by omega), by omega, by omega⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e]; exact Nat.mod_eq_of_lt sp.isLt
    have hs32 : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat + 32) 8 = sl.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout2 (by omega) (by omega), by omega, by omega⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e]; exact Nat.mod_eq_of_lt sl.isLt
    have hsbp : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout2 (by omega) (by omega), by omega, by omega⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e]; exact Nat.mod_eq_of_lt (s.regs 5).isLt
    have hsq : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat - 16) 8 = q.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      simp only [Janus.Arm64.Memory.readLE_writeLE_self]
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e]; exact Nat.mod_eq_of_lt q.isLt
    have hacc2 : ∀ a n w, ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE
        ((s.regs 4).toNat - 96) 8 4771679).accessible a n w = s.mem.accessible a n w := by
      intro a n w
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hMF.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hfr.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
    have hret2 : ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE
        ((s.regs 4).toNat - 96) 8 4771679).readLE ((s.regs 4).toNat - 96) 8 = 4771679 := by
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    have hfm2 : MemFrame m2 ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE
        ((s.regs 4).toNat - 96) 8 4771679) [((s.regs 4).toNat - 16, (s.regs 4).toNat - 8),
          ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by
      janus_frame
    generalize ((Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 16) 8 q.toNat).writeLE
        ((s.regs 4).toNat - 96) 8 4771679) = M2 at hacc2 hret2 hfm2 hrd hs8 hs16 hs24 hs32 hsq hsbp ⊢
    have hWg : Outside ((s.regs 14).toNat + 16) 8 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    have hgM2 : M2.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
      hrd _ _ hgR hgo2 hWg
    refine ReachesRet.call (hmv (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)]) (b - blockSize sl.toNat true))
      (by rfl) ⟨?eq, ?lm, ?inp, ?ld⟩ ?cont
    case eq =>
      simp only [MemAmd64.EqPre, MemAmd64.CallOK, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, calleeStack,
        MapAmd64.calleeStack, MemAmd64.calleeStack, hrsp, MapAmd64.keepABI_apply, or_true, if_true, regG, regSP, stackguard0Offset, Janus.Amd64.GoABI.stackguard0]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [regG, regSP, stackguard0Offset, Janus.Amd64.GoABI.stackguard0, setRegF_apply, callRegs64_apply, MapAmd64.keepABI_apply, reduceIte, Nat.reduceEqDiff, or_true, if_true, hrsp]; omega
      · simp only [regG, regSP, stackguard0Offset, Janus.Amd64.GoABI.stackguard0, setRegF_apply, callRegs64_apply, MapAmd64.keepABI_apply, reduceIte, Nat.reduceEqDiff, or_true, if_true, hrsp]; rw [hacc2]; exact hgr
      · simp only [regG, regSP, stackguard0Offset, Janus.Amd64.GoABI.stackguard0, setRegF_apply, callRegs64_apply, MapAmd64.keepABI_apply, reduceIte, Nat.reduceEqDiff, or_true, if_true, hrsp]; rw [hgM2]; omega
      · omega
      · omega
      · omega
      · rw [hacc2]; exact Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
      · rfl
      · trivial
      · rw [hret2]; omega
      · try simp only [regG, regSP, stackguard0Offset, Janus.Amd64.GoABI.stackguard0, setRegF_apply, callRegs64_apply, MapAmd64.keepABI_apply, reduceIte, Nat.reduceEqDiff, or_true, if_true, hrsp]
        simp only [outside_cons, outside_nil, and_true]; omega
    case lm =>
      simp only [LiveMemAt64, liveWin64, calleeStack64, MapAmd64.calleeStack, MemAmd64.calleeStack, setRegF_apply, callRegs64_apply,
        reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero,
        MapAmd64.keepABI_apply]
      refine ⟨hokv q.toNat, ?_, ?_, ?_⟩
      · exact RtInv.inv_frame' hfm2 (by
          intro r hr
          left
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl <;> exact Outside.of_sub hout (by omega) (by omega)) hInv2
      · intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | hr
        · have h := hLs r hr
          simp only [outside_cons, outside_nil, and_true, outside_append] at h ⊢
          omega
        · subst hr
          unfold Apart at hAw
          simp only [outside_cons, outside_nil, and_true, outside_append]
          omega
      · intro r hr
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_singleton] at hr
        rcases hr with (rfl | rfl) | rfl <;> exact Outside.of_sub hout (by omega) (by omega)
    case inp =>
      simp only [LiveDest64, MemAmd64.Input, calleeStack64, MapAmd64.calleeStack, MemAmd64.calleeStack, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply]
      refine ⟨hsp48, ?_, ?_⟩
      · rw [hacc2]; exact hsacc
      · simp only [outside_cons, outside_nil, and_true]; omega
    case ld =>
      simp only [LiveDest64, MemAmd64.Input, calleeStack64, MapAmd64.calleeStack, MemAmd64.calleeStack, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply]
      refine ⟨by omega, ?_, ?_, Or.inl ?_, ?_⟩
      · rw [hacc2]; exact Arm64.Memory.accessible_mono _ hQacc (by omega) (by omega)
      · unfold Apart at hAw
        simp only [outside_cons, outside_nil, and_true]; omega
      · exact ⟨(q.toNat, q.toNat + blockSize sl.toNat true), by simp, Nat.le_refl _, by omega⟩
      · unfold Apart at hAw
        simp only [outside_cons, outside_nil, and_true]; omega
    case cont =>
      intro s3 hpc3 ⟨j3, f3, x3, y3, m3, z3, k3, hs3, hfr3, hlf3, hinv3, hcp3⟩
      subst hs3
      simp only [calleeStack64, MapAmd64.calleeStack, MemAmd64.calleeStack, setRegF_apply, callRegs64_apply, reduceIte,
        Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero,
        MapAmd64.keepABI_apply, liveWin64, List.append_nil] at hfr3
      have hinv3' : R.inv (b - blockSize sl.toNat true) (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)])
          (s.regs 14).toNat (view R.rt (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)]) m3) := by
        simpa only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply] using hinv3
      have hcp3' : Mem.Copied M2 m3 q.toNat sp.toNat sl.toNat := by
        simpa only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply] using hcp3
      clear hinv3 hcp3 hlf3
      simp only [retState64, retAddrOf, setRegF_apply, reduceIte, Nat.reduceEqDiff, hrsp, hret2]
      have hgm3 : m3.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
        rw [hfr3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          refine ⟨⟨hgR, ?_, ?_⟩, ?_⟩
          · omega
          · omega
          · have := InRanges.disjoint hInR hgR
            omega)]
        exact hgM2
      have hM2acc : M2.accessible ((s.regs 4).toNat - 4192) (4192 + 72) true = true := by
        rw [hacc2]; exact hacc
      have hM2accF : M2.accessible ((s.regs 4).toNat - 4192) (4192 + 72) false = true :=
        Arm64.Memory.accessible_weaken _ hM2acc
      have hqpos : 0 < q.toNat := by
        obtain ⟨r, hr, h1, h2⟩ := hInR
        have := hrt0 r hr
        omega
      simp only [Apart] at hAw hAn h_apart
      clear hret2 hfm2
      janus64_run [hgm3] until [Extracted.program.contractAddr "runtime.newobject"]
      have hNT1 : s.mem.readLE numErrType 8 = 48 := by
        rw [h_rodata _ _ (by decide)]; decide
      have hNT2 : s.mem.readLE (numErrType + 8) 8 ≠ 0 := by
        rw [h_rodata _ _ (by decide)]; decide
      have hrd3 : ∀ a n, Outside a n R.rt → Outside a n R2.priv →
          Outside a n [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] →
          Outside a n [(q.toNat, q.toNat + sl.toNat)] → m3.readLE a n = s.mem.readLE a n := by
        intro a n h1 h2 h3 h4
        rw [hfr3.readLE a n (by
          simp only [outside_append, outside_cons, outside_nil, and_true] at h3 ⊢
          exact ⟨⟨h1, by omega, by omega⟩, by simpa using h4⟩)]
        exact hrd a n h1 h2 (by simpa using h3 |> fun h => by simp only [outside_cons, outside_nil, and_true] at h3 ⊢; omega)
      have hacc4 : ∀ a n w, (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE
          ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).accessible a n w
          = s.mem.accessible a n w := by
        intro a n w
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        rw [hfr3.accessible, hacc2]
      have hq8 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat + 8) 8 = fp.toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hfr3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
        exact hs8
      have hq16 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat + 16) 8 = fl.toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hfr3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
        exact hs16
      have hq24 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat + 24) 8 = sp.toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hfr3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
        exact hs24
      have hq32 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat + 32) 8 = sl.toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hfr3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
        exact hs32
      have hqbp : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hfr3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
        exact hsbp
      have hq24q : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat - 24) 8 = q.toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [e]; exact Nat.mod_eq_of_lt q.isLt
      have hq40 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat - 40) 8 = sl.toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [e]; exact Nat.mod_eq_of_lt sl.isLt
      have hret4 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 4).toNat - 96) 8 = 4771726 := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      have hg4 : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact hgm3
      have hoN' := hoN
      simp only [outside_cons, outside_nil, and_true] at hoN'
      have hdq := InRanges.disjoint hInR hnR
      have hNTm3 : ∀ k, k = 0 ∨ k = 8 → m3.readLE (numErrType + k) 8 = s.mem.readLE (numErrType + k) 8 := by
        intro k hk
        refine hrd3 _ _ (Outside.of_sub hnR (by omega) (by omega)) (Outside.of_sub hnP (by omega) (by omega)) ?_ ?_
        · simp only [outside_cons, outside_nil, and_true]; omega
        · simp only [outside_cons, outside_nil, and_true]; omega
      have hNT1' : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE numErrType 8 = 48 := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        have := hNTm3 0 (Or.inl rfl)
        simp only [Nat.add_zero] at this
        rw [this]; exact hNT1
      have hNT2' : (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726).readLE (numErrType + 8) 8 ≠ 0 := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hNTm3 8 (Or.inr rfl)]; exact hNT2
      have hfm4 : MemFrame m3 (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726) [((s.regs 4).toNat - 40, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16),
          ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by
        janus_frame
      generalize (((Arm64.Memory.writeLE m3 ((s.regs 4).toNat - 40) 8 sl.toNat).writeLE ((s.regs 4).toNat - 24) 8 q.toNat).writeLE ((s.regs 4).toNat - 96) 8 4771726) = M4 at hacc4 hq8 hq16 hq24 hq32 hqbp hq24q hq40 hret4 hg4 hNT1' hNT2' hfm4 ⊢
      have hnum : (5077152 : Nat) = numErrType := by decide
      refine ReachesRet.call (hnew (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)]) (b - blockSize sl.toNat true))
        (by rfl) ⟨⟨?cok, ?tok, ?tsz⟩, ⟨?gok, ?gout⟩, ?ok, ?inv, ?cost, ?sep1, ?sep2⟩ ?cont4
      case cok =>
        simp only [CallOK64, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply, calleeStack64, MapAmd64.calleeStack, liveWin64]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hret4]; omega
        · omega
        · omega
        · omega
        · rw [hacc4]; exact Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
      case tok =>
        simp only [TypeOK, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply, calleeStack64, MapAmd64.calleeStack, liveWin64]
        refine ⟨by decide, ?_⟩
        rw [hacc4]; exact Arm64.Memory.accessible_mono _ h_data3 (by decide) (by decide)
      case tsz =>
        simp only [typSize, maxAlloc, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply, calleeStack64, MapAmd64.calleeStack, liveWin64]
        rw [hnum, hNT1']; decide
      case gok =>
        simp only [GuardOK64, setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, hrsp, regG, regSP, or_false, or_self, or_true, if_true, if_false, List.getD_cons_zero, MapAmd64.keepABI_apply, calleeStack64, MapAmd64.calleeStack, liveWin64]
        refine ⟨by omega, ?_, ?_⟩
        · rw [hacc4]; exact hgr
        · rw [hg4]; omega
      all_goals sorry

end Fv256.Amd64.SfdToError
