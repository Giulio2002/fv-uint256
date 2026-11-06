import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdEnv
import Fv256.Amd64.SfdTePre
import Fv256.Amd64.SfdTeLem

/-!
# `strconv.toError(fn, s, base, bitSize, err)` for `err == ErrSyntax` (amd64), as a callee of `strconv.ParseUint`

`ParseUint` calls `toError("ParseUint", s, 10, 64, err)` when the internal parser fails; for a syntax failure the
result is `&NumError{Func: fn, Num: cloneString(s), Err: strconv.ErrSyntax}` (a freshly allocated object, the
string copied by `mallocgc` + `memmove`).  The runtime calls are `runtime.ifaceeq` (the comparison
`err == ErrSyntax`, interface-model contract), `runtime.mallocgc`, `runtime.memmove`, `runtime.newobject` and the
write barriers (live contracts, all threaded through one `RtInv`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.Amd64.SfdEnv

namespace Fv256.Amd64.SfdToError




theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

set_option hygiene false in
set_option maxRecDepth 20000 in
/-- the proof of `te_sum0`/`te_sum1` after the introduction of the precondition (shared; the two theorems differ in the
write-barrier-flag hypothesis `hfl`, which closes the branches of the other flag value) -/
macro "te_body" : tactic => `(tactic| (
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
    rw [hszS, hSacc]; exact hSa
  have hcmp := (hl.regular S.mem (S.regs 14) T synConst synConst hpre0.1 hTty hregS hndS hxacc hxacc)
  have hS0 : (S.regs 0).toNat = errItab := by
    rw [hSreg.1]; simp only [BitVec.toNat_ofNat]; decide
  refine ReachesRet.call hif (by subst hS; rfl) ⟨hpre0, fun _ => ⟨by rw [hS0]; decide, ?_, ?_, ?_⟩⟩ ?_
  · rw [hS0, hSacc]; exact hIa
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
    rename_i q j2 f2 x2 y2 m2 z2 k2 hLF hMF hApA hInR hQ48 hQacc hQa8 hQa16 hQz hQsl hAp hInv2 hAw hAn hAwb hAe
    try clear hTS hregS hndS hszS
    have hrsp : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := hs496
    have hgm2 : m2.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      rw [hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgR, ?_, ?_⟩ <;> omega)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hgm
    have hqpos : 0 < q.toNat := by
      obtain ⟨r, hr, h1, h2⟩ := hInR
      have := hrt0 r hr
      omega
    have hgq := InRanges.disjoint hInR hgR
    have hdq := InRanges.disjoint hInR hnR
    have hoN' := hoN
    simp only [outside_cons, outside_nil, and_true] at hoN'
    have hnum : numErrType = 5077152 := by decide
    have hwbn : wbFlag = 6156064 := by decide
    have hesn : strconvErrSyntax = 5996272 := by decide
    rw [hwbn] at hwbacc
    rw [hesn] at heacc
    rw [hnum] at hoN' hdq hNT1 hNT2
    simp only [Apart] at hAw hAn h_apart
    have hNT2' : s.mem.readLE 5077160 8 ≠ 0 := by simpa using hNT2
    have hNT2b : (s.mem.readLE 5077160 8 == 0) = false := by simp [hNT2']
    have herr : Extracted.dataAddr.«go:itab.internal/strconv.Error,error» = 5183968 := by decide
    janus64_run [hgm2, hNT2b, herr] until [te + 0xce] calls [hmv, hnew.pos]
    janus64_run [hgm2, hNT2b, herr] calls [hnew.pos, hwb1, hwb2]
    all_goals
      first
      | (exfalso
         have herr : Extracted.dataAddr.«go:itab.internal/strconv.Error,error» = 5183968 := by decide
         first
         | exact absurd (by decide : 18446744073704367648 - (18446744073709551616 - errItab) = 0) (by assumption)
         | omega
         | (simp only [errItab, herr] at *; omega))
      | skip
    all_goals first
      | (exfalso; te_flags; done)
      | skip
    run_tac do
      Lean.logInfo m!"D goals {(← Lean.Elab.Tactic.getGoals).length}"
    all_goals
      refine te_post_intro ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?F (fun hF => ⟨q.toNat, _, ?_, rfl, ?obj⟩)
      case F =>
        obtain ⟨f0, f1, f2, f3, f4, f5⟩ := inRanges_fields (‹InRanges _ 48 R.rt›) (rs' := R.rt) (fun r hr => hr)
        te_frame
      case obj =>
        refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8, ?c9, ?c10, ?c11, ?c12⟩
        case c1 => assumption
        case c2 => rw [blockSize48]; assumption
        case c3 => assumption
        case c4 =>
          simp only [apartAll_append, apartAll_cons, apartAll_nil, and_true, blockSize48, Nat.add_sub_cancel_left]
          exact ‹ApartAll _ 48 L ∧ _›
        all_goals
          rw [hesn] at hsRe hePr hoE
          have eR0 : Outside 5996272 8 R.rt := Outside.of_sub hsRe (by decide) (by decide)
          have eR1 : Outside 5996280 8 R.rt := Outside.of_sub hsRe (by decide) (by decide)
          have eP0 : Outside 5996272 8 R2.priv := Outside.of_sub hePr (by decide) (by decide)
          have eP1 : Outside 5996280 8 R2.priv := Outside.of_sub hePr (by decide) (by decide)
          simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hoE
          have hA := hAe
          simp only [Apart, hesn] at hA
          have hA2 := (by with_reducible assumption : Apart strconvErrSyntax 16 _ 48)
          simp only [Apart, hesn] at hA2
          have hA3 := (‹ApartAll _ 48 L ∧ Apart _ 48 _ _›).2
          simp only [Apart] at hA3
        case c5 => te_walk
        case c6 => te_walk
        case c7 => te_walk
        case c8 => te_walk
        case c9 => rw [hesn]; te_walk
        case c10 => rw [hesn]; te_walk
        case c12 => te_inv
        case c11 =>
          intro k hk
          exact te_copy (hM := rfl) (hLF := by with_reducible assumption) (hApt := hA3) (hk := hk) (hsl := hQsl)
            (by te_omega) (by te_omega) (by te_omega) (by with_reducible assumption)
            (te_src hLF hMF hspR hk hsdisj (te_hfr hfr hspP hk hdep hsdisj))
      all_goals first | rfl | (simp [hx15, hdf]; done) | skip
  all_goals (exfalso; exact absurd (by decide : 18446744073704367648 - (18446744073709551616 - errItab) = 0) (by assumption))
  ))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_sum0 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
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
    Summary (Extracted.program.link impl) te (fun s => TePre R R2 T b L fp fl sp sl s ∧ s.mem.readLE 6156064 4 = 0) (TePost R R2 b L fp fl sp sl) := by
  intro s hpc ⟨⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, h7, h9, h10, hsl1, hsl2, hg, ⟨hlow, hnw, hacc⟩, hal, hNT1, hNT2, hNa, hIa, hSa, hdep, hc2,
    hout, hinv, hLs, hbud, hTd, hTty, hTreg, hTnd, hTsz, hoI, hoS, hoE, hoW, hoN, hprR, hLpr, hnR, hwR, hsRe, hokm, hokn, hokv, hokb1, hokb2, hsacc, hsp48, hsdisj, hgdis, hgR, hrt0, hnP, hwP, hePr, hwbacc, heacc, hspR, hspP⟩, hfl⟩
  te_body

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_sum1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
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
    Summary (Extracted.program.link impl) te (fun s => TePre R R2 T b L fp fl sp sl s ∧ ¬ s.mem.readLE 6156064 4 = 0) (TePost R R2 b L fp fl sp sl) := by
  intro s hpc ⟨⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, h7, h9, h10, hsl1, hsl2, hg, ⟨hlow, hnw, hacc⟩, hal, hNT1, hNT2, hNa, hIa, hSa, hdep, hc2,
    hout, hinv, hLs, hbud, hTd, hTty, hTreg, hTnd, hTsz, hoI, hoS, hoE, hoW, hoN, hprR, hLpr, hnR, hwR, hsRe, hokm, hokn, hokv, hokb1, hokb2, hsacc, hsp48, hsdisj, hgdis, hgR, hrt0, hnP, hwP, hePr, hwbacc, heacc, hspR, hspP⟩, hfl⟩
  te_body

theorem summary_split {p : Janus.Amd64.Program} {e : Nat} {P : State → Prop} {c : State → Prop} {Q : State → State → Prop}
    (h0 : Summary p e (fun s => P s ∧ c s) Q) (h1 : Summary p e (fun s => P s ∧ ¬ c s) Q) : Summary p e P Q := by
  intro s hpc hP
  by_cases hc : c s
  · exact h0 s hpc ⟨hP, hc⟩
  · exact h1 s hpc ⟨hP, hc⟩

theorem te_sum (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
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
    Summary (Extracted.program.link impl) te (TePre R R2 T b L fp fl sp sl) (TePost R R2 b L fp fl sp sl) := by
  summary_split (c := fun s => s.mem.readLE 6156064 4 = 0)
    (te_sum0 impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2)
    (te_sum1 impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2)
end Fv256.Amd64.SfdToError
