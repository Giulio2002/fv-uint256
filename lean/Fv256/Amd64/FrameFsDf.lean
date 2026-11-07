import Janus.Amd64.Exec
import Lean

/-!
# U-FRAME-FSDF: `Exec` never writes `fsBase` and writes `df` only by `popfq` / `setDF`

Extracted-free. `exec_fr`: every instruction other than `popfq` and `setDF` (`CLD`/`STD`) keeps `fsBase` and `df`.
The `Steps` lift (`Steps_fr`) needs a decidable check that the program's code decodes to neither at any byte offset
(`FrameFsDf.Check`). The ordinary `Steps` never include a stub/exit transfer, so the FFI paths are not involved.
-/
open Janus Janus.Amd64

namespace Fv256.FrameFsDf

/-- the frame fact -/
abbrev Fr (s t : State) : Prop := t.fsBase = s.fsBase ∧ t.df = s.df

theorem Fr.refl (s : State) : Fr s s := ⟨rfl, rfl⟩
theorem Fr.trans {a b c : State} (h1 : Fr a b) (h2 : Fr b c) : Fr a c := ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem movsIter_aux (sz : Nat) : ∀ (k : Nat) (s s' : State), movsIter sz k s = .ok s' → s'.fsBase = s.fsBase ∧ s'.df = s.df
  | 0, s, s', h => by cases h; exact Fr.refl _
  | k + 1, s, s', h => by
    unfold movsIter at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact (movsIter_aux sz k _ _ h : Fr _ _)

theorem movsIterB_aux (sz : Nat) : ∀ (k : Nat) (s s' : State), movsIterB sz k s = .ok s' → s'.fsBase = s.fsBase ∧ s'.df = s.df
  | 0, s, s', h => by cases h; exact Fr.refl _
  | k + 1, s, s', h => by
    unfold movsIterB at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact (movsIterB_aux sz k _ _ h : Fr _ _)

theorem stosIter_aux (sz v : Nat) : ∀ (k : Nat) (s s' : State), stosIter sz v k s = .ok s' → s'.fsBase = s.fsBase ∧ s'.df = s.df
  | 0, s, s', h => by cases h; exact Fr.refl _
  | k + 1, s, s', h => by
    unfold stosIter at h
    split at h
    · cases h
    · exact (stosIter_aux sz v k _ _ h : Fr _ _)

theorem stosIterB_aux (sz v : Nat) : ∀ (k : Nat) (s s' : State), stosIterB sz v k s = .ok s' → s'.fsBase = s.fsBase ∧ s'.df = s.df
  | 0, s, s', h => by cases h; exact Fr.refl _
  | k + 1, s, s', h => by
    unfold stosIterB at h
    split at h
    · cases h
    · exact (stosIterB_aux sz v k _ _ h : Fr _ _)


open Lean Elab Tactic Meta in
/-- for every hypothesis `H args = Except.ok t` in the context with a lemma `Fv256.FrameFsDf.H_fr` (`H args = .ok t → frame`), add the fact -/
elab "fr_collect" : tactic => withMainContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOf ``Except.ok do continue
    let some c := lhs.getAppFn.constName? | continue
    let nm := `Fv256.FrameFsDf ++ (Name.mkSimple (c.getString! ++ "_fr"))
    unless (← getEnv).contains nm do continue
    let some pf ← (try some <$> mkAppM nm #[ld.toExpr] catch _ => pure none) | continue
    let g ← getMainGoal
    let g ← g.assert `fr (← inferType pf) pf
    let (_, g) ← g.intro1
    replaceMainGoal [g]

theorem movsIter_fr {sz k : Nat} {s s' : State} (h : movsIter sz k s = .ok s') : s'.fsBase = s.fsBase ∧ s'.df = s.df := movsIter_aux sz k s s' h
theorem movsIterB_fr {sz k : Nat} {s s' : State} (h : movsIterB sz k s = .ok s') : s'.fsBase = s.fsBase ∧ s'.df = s.df := movsIterB_aux sz k s s' h
theorem stosIter_fr {sz v k : Nat} {s s' : State} (h : stosIter sz v k s = .ok s') : s'.fsBase = s.fsBase ∧ s'.df = s.df := stosIter_aux sz v k s s' h
theorem stosIterB_fr {sz v k : Nat} {s s' : State} (h : stosIterB sz v k s = .ok s') : s'.fsBase = s.fsBase ∧ s'.df = s.df := stosIterB_aux sz v k s s' h

set_option hygiene false in
/-- split the matches of `h : (… ) = .ok t`, then close by the frame lemmas of the callee helpers (`@[local simp]`) -/
macro "fr_helper" : tactic =>
  `(tactic| ((try unfold Fr) <;> (repeat' (first | split at h | dsimp only at h)) <;>
    first
    | (fr_collect; assumption)
    | (fr_collect; obtain rfl := Except.ok.inj h; (try unfold State.putReg) <;> (repeat' split) <;> first | exact ⟨rfl, rfl⟩ | simp_all)
    | (cases h <;> done)
    | simp_all))

attribute [local simp] State.setReg State.setFlags State.setRip State.putReg State.putHigh State.setXmm State.setV
  State.setYmmHi State.setZmmHi State.setXmmLow State.advanceUndef ExecSSE.raiseMx

theorem writeLoc_fr {s : State} {n : W64} {w : Nat} {l : Loc} {v : BitVec w} {t : State}
    (h : writeLoc s n w l v = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold writeLoc at h; fr_helper

theorem writeX_fr {s : State} {n : W64} {al : Bool} {l : XLoc} {v : W128} {t : State}
    (h : writeX s n al l v = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold writeX at h; fr_helper

theorem writeV_fr {s : State} {n : W64} {l : Nat} {al : Bool} {d : XLoc} {v : Nat} {t : State}
    (h : writeV s n l al d v = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold writeV at h; fr_helper

theorem push64_fr {s : State} {v : W64} {t : State}
    (h : push64 s v = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold push64 at h; fr_helper

theorem branchTo_fr {s : State} {v : W64} {t : State}
    (h : branchTo s v = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold branchTo at h; fr_helper

theorem execAlu_fr {s : State} {n : W64} {op : AluOp} {w : Nat} {d : Loc} {sr : Src} {t : State}
    (h : execAlu s n op w d sr = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execAlu at h; fr_helper

theorem execUnary_fr {s : State} {n : W64} {op : UnOp} {w : Nat} {d : Loc} {t : State}
    (h : execUnary s n op w d = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execUnary at h; fr_helper

theorem execMul1_fr {s : State} {n : W64} {sg : Bool} {w : Nat} {d : Loc} {t : State}
    (h : execMul1 s n sg w d = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execMul1 at h; fr_helper

theorem execImul_fr {s : State} {n : W64} {w d : Nat} {a : Loc} {b : Src} {t : State}
    (h : execImul s n w d a b = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execImul at h; fr_helper

theorem execDiv_fr {s : State} {n : W64} {sg : Bool} {w : Nat} {d : Loc} {t : State}
    (h : execDiv s n sg w d = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execDiv at h; fr_helper

theorem execDivRef_fr {s : State} {n : W64} {sg : Bool} {w : Nat} {d : Loc} {t : State}
    (h : execDivRef s n sg w d = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execDivRef at h; fr_helper

theorem execShift_fr {s : State} {n : W64} {op : ShOp} {w : Nat} {d : Loc} {c : Src} {t : State}
    (h : execShift s n op w d c = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execShift at h; fr_helper

theorem execRcx_fr {s : State} {n : W64} {l : Bool} {w : Nat} {d : Loc} {c : Src} {t : State}
    (h : execRcx s n l w d c = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execRcx at h; fr_helper

theorem execShd_fr {s : State} {n : W64} {l : Bool} {w : Nat} {d : Loc} {sr : Nat} {c : Src} {t : State}
    (h : execShd s n l w d sr c = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execShd at h; fr_helper

theorem execBit_fr {s : State} {n : W64} {op : BitOp} {w : Nat} {d : Loc} {o : Src} {t : State}
    (h : execBit s n op w d o = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execBit at h; fr_helper

theorem execCount_fr {s : State} {n : W64} {op : CntOp} {w d : Nat} {a : Loc} {t : State}
    (h : execCount s n op w d a = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execCount at h; fr_helper

theorem execShiftx_fr {s : State} {n : W64} {op : ShOp} {w d : Nat} {a : Loc} {c : Nat} {t : State}
    (h : execShiftx s n op w d a c = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execShiftx at h; fr_helper

theorem evex_fr (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : EvexI XLoc Loc Addr) (s' : State)
    (h : ExecEVEX.exec s next pc ea i = .ok s') : Fr s s' := by
  cases i <;> simp only [ExecEVEX.exec, ExecEVEX.done, ExecEVEX.doneFP] at h <;> fr_helper

theorem sse_fr (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : SseI XLoc Loc Addr) (s' : State)
    (h : ExecSSE.exec s next pc ea i = .ok s') : Fr s s' := by
  cases i <;> simp only [ExecSSE.exec, ExecSSE.doneX, ExecSSE.doneFP] at h <;> fr_helper

theorem avx_fr (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : AvxI XLoc Loc Addr) (s' : State)
    (h : ExecAVX.exec s next pc ea i = .ok s') : Fr s s' := by
  cases i <;> simp only [ExecAVX.exec, ExecAVX.doneV, ExecAVX.doneFPV, ExecAVX.doneS, ExecAVX.maskmovExec,
    ExecAVX.gatherExec] at h <;> fr_helper

theorem crypto_fr (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : CryptoI XLoc Loc) (s' : State)
    (h : ExecCrypto.exec s next pc ea i = .ok s') : Fr s s' := by
  cases i <;> simp only [ExecCrypto.exec] at h <;> fr_helper

theorem x87_fr (s : State) (pc : Nat) (next : W64) (op : X87.Op) (addr : Option Nat) (cond : Nat → Option Bool)
    (s' : State) (h : X87.exec s pc next op addr cond = .ok s') : Fr s s' := by
  cases op <;> simp only [X87.exec, X87.execWaiting, X87.fin] at h <;> fr_helper

theorem execAndn_fr {s : State} {n : W64} {w d s1 : Nat} {a : Loc} {t : State}
    (h : execAndn s n w d s1 a = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execAndn at h; fr_helper

theorem execBlsx_fr {s : State} {n : W64} {op w d : Nat} {a : Loc} {t : State}
    (h : execBlsx s n op w d a = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execBlsx at h; fr_helper

theorem execBextr_fr {s : State} {n : W64} {w d : Nat} {a : Loc} {c : Nat} {t : State}
    (h : execBextr s n w d a c = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execBextr at h; fr_helper

theorem execBzhi_fr {s : State} {n : W64} {w d : Nat} {a : Loc} {c : Nat} {t : State}
    (h : execBzhi s n w d a c = .ok t) : t.fsBase = s.fsBase ∧ t.df = s.df := by
  unfold execBzhi at h; fr_helper

/-- the instructions whose execution is covered: all but `popfq`, `setDF` (also under `LOCK`) -/
def NoDf : Instr → Bool
  | .popfq => false
  | .setDF _ => false
  | .locked i _ _ => NoDf i
  | _ => true

/-- Every instruction except `popfq` and `setDF` keeps `fsBase` and `df`. -/
theorem exec_fr (i : Instr) (len : Nat) (s s' : State) (hn : NoDf i = true)
    (h : exec i len s = .ok s') : Fr s s' := by
  cases i with
  | popfq => simp [NoDf] at hn
  | setDF b => simp [NoDf] at hn
  | sse i => exact sse_fr _ _ _ _ i _ h
  | avx i => exact avx_fr _ _ _ _ i _ h
  | evex i => exact evex_fr _ _ _ _ i _ h
  | crypto i => exact crypto_fr _ _ _ _ i _ h
  | x87 op m => exact x87_fr _ _ _ op _ _ _ h
  | locked j a size =>
    simp only [exec] at h
    split at h
    · cases h
    · exact exec_fr j len s s' (by simpa [NoDf] using hn) h
  | _ =>
    clear hn
    simp only [exec, fpDone] at h
    fr_helper
termination_by i
decreasing_by all_goals (simp_wf; subst_vars; simp; try omega)

/-! ## The decidable code check and the `Steps` lift -/

/-- the instruction decoded from `bytes` (if any) is not `popfq` / `setDF` -/
def okAt (bytes : List Nat) : Bool :=
  match decode bytes with
  | some (i, _) => NoDf i
  | none => true

/-- every byte offset of the segment decodes (as `Program.fetch` would deliver it) to a covered instruction -/
def segOk (seg : Janus.Amd64.Segment) : Bool :=
  (List.range seg.bytes.length).all fun o => okAt ((seg.bytes.drop o).take 15)

/-- the code check: no byte offset of any segment decodes to `popfq` or `setDF` -/
def codeOk (segs : List Janus.Amd64.Segment) : Bool := segs.all segOk

theorem fetchIn_ok : ∀ {segs : List Janus.Amd64.Segment} {pc : Nat} {w : List Nat},
    codeOk segs = true → Janus.Amd64.Program.fetchIn segs pc = some w → okAt w = true
  | [], _, _, _, h => by simp [Janus.Amd64.Program.fetchIn] at h
  | seg :: rest, pc, w, hc, h => by
    simp only [codeOk, List.all_cons, Bool.and_eq_true] at hc
    unfold Janus.Amd64.Program.fetchIn at h
    split at h
    · rename_i hin
      cases h
      have h1 := hc.1
      simp only [segOk, List.all_eq_true, List.mem_range] at h1
      exact h1 (pc - seg.base) (by omega)
    · exact fetchIn_ok (by simpa [codeOk] using hc.2) h

/-- `fsBase` is never written by `exec` (any instruction, including `popfq` / `setDF`; `FFI` stubs are not `Steps`). -/
theorem exec_fs (i : Instr) (len : Nat) (s s' : State) (h : exec i len s = .ok s') : s'.fsBase = s.fsBase := by
  by_cases hn : NoDf i = true
  · exact (exec_fr i len s s' hn h).1
  · cases i with
    | popfq =>
      simp only [exec] at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h; rfl
    | setDF b => simp only [exec] at h; cases h; rfl
    | locked j a size =>
      simp only [exec] at h
      split at h
      · cases h
      · exact exec_fs j len s s' h
    | _ => simp [NoDf] at hn
termination_by i
decreasing_by all_goals (simp_wf; subst_vars; simp; try omega)

theorem Steps_fs {p : Janus.Amd64.Program} {s s' : State} {k : Nat} (h : Janus.Amd64.Program.Steps p s k s') :
    s'.fsBase = s.fsBase := by
  induction h with
  | refl => rfl
  | @step s s₁ s₂ k w hx hs hf hst _ ih =>
    refine ih.trans ?_
    unfold Amd64.step at hst
    split at hst
    · rename_i i len hd
      exact exec_fs i len s s₁ hst
    · cases hst

theorem Steps_fr {p : Janus.Amd64.Program} (hc : codeOk p.segments = true) {s s' : State} {k : Nat}
    (h : Janus.Amd64.Program.Steps p s k s') : Fr s s' := by
  induction h with
  | refl => exact Fr.refl _
  | @step s s₁ s₂ k w hx hs hf hst _ ih =>
    refine Fr.trans ?_ ih
    have hw : okAt w = true := fetchIn_ok hc hf
    unfold Amd64.step at hst
    revert hw
    unfold okAt
    split
    · rename_i i len hd
      simp only [hd] at hst
      intro hn
      exact exec_fr i len s s₁ hn hst
    · simp_all

/-! ## Negative sanity checks: the check rejects `std`, `cld`, `popfq` (also under `lock`-free single-byte forms) -/

def segStd : Janus.Amd64.Segment := { name := "std", base := 0x1000, bytes := [0xfd] }
def segCld : Janus.Amd64.Segment := { name := "cld", base := 0x1000, bytes := [0xfc] }
def segPopf : Janus.Amd64.Segment := { name := "popf", base := 0x1000, bytes := [0x9d] }
def segMix : Janus.Amd64.Segment := { name := "mix", base := 0x1000, bytes := [0x48, 0x89, 0xd8, 0x90, 0xfd, 0xc3] }
def segOkTiny : Janus.Amd64.Segment := { name := "ok", base := 0x1000, bytes := [0x48, 0x89, 0xd8, 0x90, 0xc3] }

theorem neg_std : codeOk [segStd] = false := by decide +kernel
theorem neg_cld : codeOk [segCld] = false := by decide +kernel
theorem neg_popf : codeOk [segPopf] = false := by decide +kernel
theorem neg_mix : codeOk [segMix] = false := by decide +kernel
theorem pos_tiny : codeOk [segOkTiny] = true := by decide +kernel

end Fv256.FrameFsDf
