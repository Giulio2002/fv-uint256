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
  Outside ((s.regs 14).toNat + 16) 8 R.rt

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
    hout, hinv, hLs, hbud, hTd, hTty, hTreg, hTnd, hTsz, hoI, hoS, hoE, hoW, hoN, hprR, hLpr, hnR, hwR, hokm, hokn, hokv, hokb1, hokb2, hsacc, hsp48, hsdisj, hgdis, hgR⟩
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
  · intro s' hpc' ⟨r, x, y, fl, m', zh, kr, hs', hfr, henv', hres⟩
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
    rename_i q j2 f2 x2 y2 m2 z2 k2 hLF hMF hApA hInR hQ48 hQacc hQa8 hQa16 hQz hQsl hAp hInv2 hAw hAn
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
    all_goals trace_state
    refine ReachesRet.call (hmv (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)]) (b - blockSize sl.toNat true))
      (by rfl) ⟨?eq, ?lm, ?inp, ?ld⟩ ?cont
    case eq =>
      simp only [MemAmd64.EqPre, MemAmd64.CallOK, Janus.Contracts.CallOK64, StackGuardOK, setRegF_apply, reduceIte, Nat.reduceEqDiff]
      all_goals trace_state
      all_goals sorry
    all_goals sorry
