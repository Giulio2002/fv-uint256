import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.Iface Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type

namespace Fv256.Arm64.UnmarshalSSZMain

abbrev ev : Nat := Extracted.dataAddr.«github.com/holiman/uint256.ErrBadEncodedLength»
abbrev tErr : Nat := Extracted.dataAddr.«type:*errors.errorString»
abbrev iErr : Nat := Extracted.dataAddr.«go:itab.*errors.errorString,error»
abbrev tInt : Nat := Extracted.dataAddr.«type:int»
abbrev iWrap : Nat := Extracted.dataAddr.«go:itab.*fmt.wrapError,error»

def fmtAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x6c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).UnmarshalSSZ" 27)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).UnmarshalSSZ" 28) 0

/-- The address of the constant `32` (the third `fmt.errorf` argument), recomputed from the `ADRP`+`ADD` words. -/
def c32Addr : Nat :=
  adrpLdTarget (Extracted.entry + 0x60) (segWord Extracted.program "github.com/holiman/uint256.(*Int).UnmarshalSSZ" 24)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).UnmarshalSSZ" 25) 0

/-- The text of the error: the `ErrBadEncodedLength` text, then `": have n, want 32 bytes"`. -/
def errMsg (txt : List Nat) (n : Nat) : List Nat :=
  txt ++ ([58, 32, 104, 97, 118, 101, 32] ++ natBytes n ++ [44, 32, 119, 97, 110, 116, 32] ++ [51, 50] ++ [32, 98, 121, 116, 101, 115])

theorem decBytes_small (n : Nat) (h : n < 2 ^ 63) : decBytes (toSigned n) = natBytes n := by
  unfold decBytes toSigned
  rw [if_pos h]
  have : ¬ ((n : Int) < 0) := by omega
  rw [if_neg this]
  simp

/-- `ErrBadEncodedLength` holds an `*errors.errorString` (itab word, non-nil data word `e` pointing at the string header `(tp, tl)`). -/
def ErrHolds (m : Memory) (e tp tl : Nat) : Prop :=
  m.accessible ev 16 false = true ∧ m.readLE ev 8 = iErr ∧ m.readLE (ev + 8) 8 = e ∧ e ≠ 0 ∧
    m.accessible e 16 false = true ∧ m.readLE e 8 = tp ∧ m.readLE (e + 8) 8 = tl ∧ e + 16 ≤ 2 ^ 48 ∧
    tl + 60 ≤ 2 ^ 32 ∧ tp + tl ≤ 2 ^ 48 ∧ (tl = 0 ∨ m.accessible tp tl false = true)



/-- The bytes `[a, a+n)` are outside the stack window and either outside the runtimes' ranges or inside a live object. -/
def Untouched (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (s : State) (a n : Nat) : Prop :=
  (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ a) ∧ (Outside a n (R.rt ++ Ri.priv) ∨ InRanges a n L)

macro "frame_sub" : tactic =>
  `(tactic| (intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack] at h ⊢; grind))

def ErrPre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 4208 ∧ StackOK s 4208 24 ∧ Extracted.program.DataLoaded s.mem ∧ ErrHolds s.mem e tp tl ∧
    Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4208, s.sp.toNat + 24) :: R.rt) ∧
    LiveSep [(s.sp.toNat - 4208, s.sp.toNat + 24)] R.rt ∧ LiveSep L [(s.sp.toNat - 4208, s.sp.toNat + 24)] ∧
    R.ok (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, s.sp.toNat - 56, 3, 3] ∧
    R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ 2 * (tl + 42) + 48 ≤ bud ∧
    (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length (R.rt ++ Ri.priv)) ∧
    Outside ev 16 (R.rt ++ Ri.priv) ∧ Outside e 16 (R.rt ++ Ri.priv) ∧
    (ev + 16 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ ev) ∧ (e + 16 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ e) ∧
    (tp + tl ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ tp) ∧
    (tl = 0 ∨ Outside tp tl (R.rt ++ Ri.priv) ∨ InRanges tp tl L) ∧
    CallerOK Ri s 112 24 ∧ H [len.toNat] (s.regs 28).toNat (s.sp.toNat - 112) (rtView Ri.priv s.mem) ∧
    Outside (s.sp.toNat - 4208) 4232 Ri.priv ∧ (∀ r ∈ Ri.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ LiveSep L Ri.priv ∧ Outside 0 1 Ri.priv ∧ Ri.depth ≤ 4096 ∧
    Untouched R Ri L s z.toNat 32 ∧ Untouched R Ri L s bp.toNat cap.toNat

theorem natBytes_len_small (n : Nat) (h : n < 2 ^ 63) : (natBytes n).length ≤ 20 := by
  have := Janus.Contracts.ErrorfConsumer.decBytes_length_le n (by omega)
  rwa [decBytes_small n h] at this

theorem call_pre' (R : RtInv) (L : List (Nat × Nat)) (b cost : Nat) (addr : Nat) (args : List Nat) (X : List (Nat × Nat))
    {s S : State} {lo hi stack nargs fr : Nat}
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + (stack + fr) < s.sp.toNat)
    (hgo : Outside ((s.regs 28).toNat + 16) 8 ((lo, hi) :: R.rt))
    (hgX : Outside ((s.regs 28).toNat + 16) 8 X)
    (hfr : MemFrame s.mem S.mem (R.rt ++ ((lo, hi) :: X))) (hg : S.regs 28 = s.regs 28)
    (hsp : S.sp.toNat + fr = s.sp.toNat) (hal : S.sp.toNat % 16 = 0)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (h8 : 8 ≤ stack) (hstk : stack ≤ S.sp.toNat)
    (hlo : lo ≤ S.sp.toNat - stack) (hhi : S.sp.toNat + 8 + 8 * nargs ≤ hi) (hhi48 : hi ≤ 2 ^ 48)
    (hacc : s.mem.accessible lo (hi - lo) true = true)
    (hwrt : LiveSep [(lo, hi)] R.rt) (hwL : LiveSep L [(lo, hi)])
    (hok : R.ok addr args) (hinv : R.inv b L (S.regs 28).toNat (view R.rt L S.mem)) (hcost : cost ≤ b) :
    CallOK S stack nargs ∧ StackRoom S stack nargs ∧
      LiveAt R addr args L b cost (S.regs 28).toNat S.mem (calleeStack S stack nargs) := by
  have hgw : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ ((lo, hi) :: X)) := by
    simp only [outside_cons, outside_append, outside_nil, and_true] at hgo hgX ⊢
    exact ⟨hgo.2, hgo.1, hgX⟩
  refine ⟨⟨h30a, h30b, hal, hstk, h8, by omega, ?_⟩, ⟨?_, ?_⟩,
    hok, hinv, hcost, LiveSep.callee hwL hlo hhi, LiveSep.calleeRt hwrt hlo hhi⟩
  · rw [hfr.accessible]
    exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · unfold Janus.Spec.GuardOK
    rw [hg]
    refine ⟨hg1, ?_, ?_⟩
    · rw [hfr.accessible]; exact hg2
    · rw [hfr.readLE _ _ hgw]; omega
  · rw [hg]
    simp only [calleeStack, outside_cons, outside_nil, and_true]
    simp only [outside_cons, outside_nil, and_true] at hgo
    omega

def ErrPost (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = iWrap ∧
    ∃ d, (s'.regs 1).toNat = d ∧ d + 32 ≤ 2 ^ 48 ∧ s'.mem.accessible d 32 true = true ∧
      s'.mem.readLE (d + 8) 8 = (errMsg (strBytes s.mem tp tl) len.toNat).length ∧
      strBytes s'.mem (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length = errMsg (strBytes s.mem tp tl) len.toNat ∧
      s'.mem.readLE (d + 16) 8 = s.mem.readLE ev 8 ∧ s'.mem.readLE (d + 24) 8 = s.mem.readLE (ev + 8) 8 ∧
      FreshFrom [(d, d + 32)] L ∧ InRanges d 32 R.rt ∧
      MemFrame s.mem s'.mem (R.rt ++ (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)])) ∧ LiveFrame s.mem s'.mem L [] ∧
      R.inv (bud - (2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48))
        (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length))
        (s.regs 28).toNat
        (view R.rt (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length)) s'.mem) ∧
      s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 ∧ s'.mem.readLE bp.toNat cap.toNat = s.mem.readLE bp.toNat cap.toNat

theorem untouched_read {R : RtInv} {Ri : IfaceModel} {L : List (Nat × Nat)} {s : State} {m : Memory} {a n : Nat}
    (h : Untouched R Ri L s a n) (hf : MemFrame s.mem m (R.rt ++ (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)])))
    (hl : LiveFrame s.mem m L []) : m.readLE a n = s.mem.readLE a n := by
  obtain ⟨h1, h2 | h2⟩ := h
  · apply hf.readLE
    simp only [outside_append, outside_cons, outside_nil, and_true] at h2 ⊢
    exact ⟨h2.1, h2.2, h1⟩
  · exact hl.readLE a n h2 (by simp)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem errblk1 (impl : List Segment) (R : RtInv) (Ri : IfaceModel) (hl : Ri.Laws) (H : RtReady)
    (hf : ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R
      tErr iErr tInt iWrap 26 fmtNum 4294967296)
    (hconv : ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H)
    (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp, len, cap]
      (fun s => len.toNat ≠ 32 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ s.regs 29 = s.sp - 8#64 ∧
        ErrPre R Ri H L bud e tp tl z bp len cap s)
      (ErrPost R Ri L bud e tp tl z bp len cap) := by
  intro ret hret s hs ⟨hlen, hlc, hc48, hfp, ⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, ⟨hv1, hv2, hv3, hv3n, hv4, hv5, hv6, he48, htl, htpb, htx⟩,
    hgo, hwrt, hwL, hok, hinv, hbud, hdataO, hevO, heO, hevW, heW, htW, htO, hc, hH, hpO, hpR, hpL, hp0, hdepth, hzU, hdU⟩
  have hc' := hc
  obtain ⟨hcEnv, hcG, hcal, hdep, hcsp, hcab, hcacc, hcout, hcgd, hcgo⟩ := hc'
  janus_intro hs
  janus_data hd [hw4]
  janus_eval_nat hFA : fmtAddr
  janus_eval_nat hC32 : c32Addr
  janus_eval_nat hTI : tInt
  janus_eval_nat hTE : tErr
  simp only [ev, iErr, Extracted.dataAddr.«github.com/holiman/uint256.ErrBadEncodedLength», Extracted.dataAddr.«go:itab.*errors.errorString,error»] at hv1 hv2 hv3 hevO hevW
  janus_run [hv2, hv3] until [Extracted.program.contractAddr "runtime.convT64"]
  refine Reaches.call (Summary.withExit hconv hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg])
      (by simp [setReg]) (by decide) (by decide), ?_⟩ ?_
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    simp (disch := janus_disch) only [rtView_writeLE]
    have e1 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by bv_omega
    simpa [e1] using hH
  intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hbox⟩
  subst hs'
  simp only [rtWrites, calleeStack, List.append_nil] at hfr
  janus_run until [Extracted.program.contractAddr "fmt.errorf"]
  obtain ⟨hb48, hbacc, hbin, hbval⟩ := hbox
  obtain ⟨rr, hrr, hrr1, hrr2⟩ := hbin
  have hsp112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by bv_omega
  have hsp56 : (s.sp - 56#64).toNat = s.sp.toNat - 56 := by bv_omega
  simp only [hsp112] at hfr
  have hbw : (r 0).toNat + 8 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ (r 0).toNat := by
    have := MemFrame.outside_mem hpO hrr; omega
  have hb0 : (r 0).toNat ≠ 0 := by
    have := MemFrame.outside_mem hp0 hrr; omega
  have hbO : Outside (r 0).toNat 8 R.rt := Outside.of_sub (hpR rr hrr) hrr1 (by omega)
  have hfm1 : MemFrame s.mem m' (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) :=
    MemFrame.trans (show MemFrame s.mem _ (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) by janus_frame) hfr (by frame_sub)
  have hLS : LiveSep L (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) := by
    intro r hr
    have h1 := hpL r hr
    have h2 := hwL r hr
    simp only [outside_append]
    exact ⟨h1, h2⟩
  have hlf1 : LiveFrame s.mem m' L [] := LiveFrame.of_win hfm1 hLS
  have hRS : LiveSep (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) R.rt := by
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · exact hpR r hr
    · subst hr; exact hwrt _ (List.mem_singleton_self _)
  have hO2 : Outside fmtAddr 256 (R.rt ++ Ri.priv) :=
    hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 2) (by decide))
  have hO3 : Outside c32Addr 256 (R.rt ++ Ri.priv) :=
    hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 3) (by decide))
  simp only [outside_append] at hO2 hO3 hevO heO
  have hTP : tl = 0 ∨ Outside tp tl (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) := by
    rcases htO with h | h | h
    · exact Or.inl h
    · right
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨h.2, by omega⟩
    · right
      obtain ⟨r, hr, h1, h2⟩ := h
      exact Outside.of_sub (hLS r hr) h1 (by omega)
  have hmsgL : ∀ M : Memory, (errMsg (strBytes M tp tl) len.toNat).length = tl + 22 + (natBytes len.toNat).length := by
    intro M; simp only [errMsg, strBytes, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]; omega
  have facts : ∀ (M : Memory) (b : Nat), MemFrame s.mem M (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) →
      b + 8 ≤ 2 ^ 48 → b ≠ 0 → M.accessible b 8 false = true → M.readLE b 8 = len.toNat →
      M.readLE (s.sp.toNat - 56) 8 = tErr → M.readLE (s.sp.toNat - 48) 8 = e →
      M.readLE (s.sp.toNat - 40) 8 = tInt → M.readLE (s.sp.toNat - 32) 8 = b →
      M.readLE (s.sp.toNat - 24) 8 = tInt → M.readLE (s.sp.toNat - 16) 8 = c32Addr →
      ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 M fmtAddr 26 (s.sp.toNat - 56) 3 3 ∧
      errorfReads M fmtAddr 26 (s.sp.toNat - 56) =
        [(fmtAddr, 26), (s.sp.toNat - 56, 48), (e, 16), (tp, tl), (b, 8), (c32Addr, 8)] ∧
      msgOf M fmtAddr 26 (s.sp.toNat - 56) = errMsg (strBytes s.mem tp tl) len.toNat ∧
      errorfCost M fmtAddr 26 (s.sp.toNat - 56) = 2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48 ∧
      operandD M (s.sp.toNat - 56) 0 = e := by
    intro M b hf' hb48 hbn hbacc' hbv hA0 hA1 hA2 hA3 hA4 hA5
    have hrd : ∀ a n, Outside a n (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) → M.readLE a n = s.mem.readLE a n :=
      fun a n h => hf'.readLE a n h
    have hacc : ∀ a n w, M.accessible a n w = s.mem.accessible a n w := fun a n w => hf'.accessible a n w
    have hW1 : ∀ a n, a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ a → Outside a n [(s.sp.toNat - 4208, s.sp.toNat + 24)] := by
      intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
    have hW2 : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ a) → Outside a n Ri.priv →
        Outside a n (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) := by
      intro a n h1 h2; simp only [outside_append]; exact ⟨h2, hW1 a n h1⟩
    have hfm : M.readLE fmtAddr 26 = fmtNum := by
      rw [hrd fmtAddr 26 (hW2 fmtAddr 26 (by omega) (Outside.of_sub hO2.2 (by omega) (by omega))), h_rodata fmtAddr 26 (by decide +kernel)]; decide +kernel
    have hv32 : M.readLE c32Addr 8 = 32 := by
      rw [hrd c32Addr 8 (hW2 c32Addr 8 (by omega) (Outside.of_sub hO3.2 (by omega) (by omega))), h_rodata c32Addr 8 (by decide +kernel)]; decide +kernel
    have hfR : Readable M fmtAddr 26 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data2 (by omega) (by omega)⟩
    have hsR : Readable M (s.sp.toNat - 56) 48 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))⟩
    have heR : Readable M e 16 := ⟨by omega, fun _ => by rw [hacc]; exact hv4⟩
    have htR : Readable M tp tl := ⟨htpb, fun hpos => by rw [hacc]; rcases htx with h | h; omega; exact h⟩
    have hq1R : Readable M b 8 := ⟨hb48, fun _ => hbacc'⟩
    have hq2R : Readable M c32Addr 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hA1' : M.readLE (s.sp.toNat - 56 + 8) 8 = e := by
      rw [show s.sp.toNat - 56 + 8 = s.sp.toNat - 48 by omega]; exact hA1
    have hA2' : M.readLE (s.sp.toNat - 56 + 16) 8 = tInt := by
      rw [show s.sp.toNat - 56 + 16 = s.sp.toNat - 40 by omega]; exact hA2
    have hA3' : M.readLE (s.sp.toNat - 56 + 24) 8 = b := by
      rw [show s.sp.toNat - 56 + 24 = s.sp.toNat - 32 by omega]; exact hA3
    have hA4' : M.readLE (s.sp.toNat - 56 + 32) 8 = tInt := by
      rw [show s.sp.toNat - 56 + 32 = s.sp.toNat - 24 by omega]; exact hA4
    have hA5' : M.readLE (s.sp.toNat - 56 + 40) 8 = c32Addr := by
      rw [show s.sp.toNat - 56 + 40 = s.sp.toNat - 16 by omega]; exact hA5
    have htp' : M.readLE e 8 = tp := by rw [hrd e 8 (hW2 e 8 (by omega) (Outside.of_sub heO.2 (by omega) (by omega)))]; exact hv5
    have htl' : M.readLE (e + 8) 8 = tl := by
      rw [hrd (e + 8) 8 (hW2 (e + 8) 8 (by omega) (Outside.of_sub heO.2 (by omega) (by omega)))]; exact hv6
    have hargs := ErrorfConsumer.argsOK_real (Env.mk tErr iErr tInt iWrap) 4294967296 M fmtAddr (s.sp.toNat - 56)
      e tp tl b c32Addr (by decide) hfm hfR hsR hA0 hA1' hv3n heR htp' htl' htR hA2' hA3' hbn
      hq1R hA4' hA5' (by decide) hq2R (by omega)
    have hn : nDec (segsOf M fmtAddr 26) = 2 := by rw [segsOf_real _ _ _ rfl hfm]; decide
    have hstr : strBytes M tp tl = strBytes s.mem tp tl := by
      apply strBytes_congr
      intro i hi
      rcases hTP with h0 | h0
      · omega
      · exact hf'.bytes (Outside.of_sub h0 (by omega) (by omega))
    have hmsg : msgOf M fmtAddr 26 (s.sp.toNat - 56) = errMsg (strBytes s.mem tp tl) len.toNat := by
      rw [msgOf_real _ _ _ _ rfl hfm, hA1', htp', htl', hA3', hA5', hbv, hv32, hstr,
        decBytes_small len.toNat (by omega)]
      have d32 : decBytes (toSigned 32) = [51, 50] := by decide
      rw [d32]; rfl
    have hmlen : (msgOf M fmtAddr 26 (s.sp.toNat - 56)).length = (errMsg (strBytes s.mem tp tl) len.toNat).length := by
      rw [hmsg]
    have hcost : errorfCost M fmtAddr 26 (s.sp.toNat - 56) = 2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48 := by
      have := hmsgL s.mem
      unfold errorfCost; rw [hmlen, if_neg (by omega)]; simp only [wrapBytes]; omega
    have hreads : errorfReads M fmtAddr 26 (s.sp.toNat - 56) =
        [(fmtAddr, 26), (s.sp.toNat - 56, 48), (e, 16), (tp, tl), (b, 8), (c32Addr, 8)] := by
      unfold errorfReads
      rw [hn]
      simp [operandD, hA1', htp', htl', hA3', hA5', List.range_succ]
    exact ⟨hargs, hreads, hmsg, hcost, by unfold operandD; exact hA1'⟩
  have hPo : ∀ a n, s.sp.toNat - 4208 ≤ a → a + n ≤ s.sp.toNat + 24 → Outside a n Ri.priv := fun a n h1 h2 =>
    Outside.of_sub hpO h1 (by omega)
  have hRo : ∀ a n, s.sp.toNat - 4208 ≤ a → a + n ≤ s.sp.toNat + 24 → Outside a n R.rt := fun a n h1 h2 =>
    Outside.of_sub (hwrt _ (List.mem_singleton_self _)) h1 (by simp only; omega)
  have hnb : (natBytes len.toNat).length ≤ 20 := natBytes_len_small len.toNat (by omega)
  have key : ∀ (S : State), MemFrame s.mem S.mem (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) → S.regs 28 = s.regs 28 →
      S.sp.toNat + 112 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 →
      S.regs 0 = (BitVec.ofNat 64 fmtAddr) → S.regs 1 = 26#64 → S.regs 2 = s.sp - 56#64 → S.regs 3 = 3#64 → S.regs 4 = 3#64 →
      S.mem.accessible (r 0).toNat 8 false = true → S.mem.readLE (r 0).toNat 8 = len.toNat →
      S.mem.readLE (s.sp.toNat - 56) 8 = tErr → S.mem.readLE (s.sp.toNat - 48) 8 = e →
      S.mem.readLE (s.sp.toNat - 40) 8 = tInt → S.mem.readLE (s.sp.toNat - 32) 8 = (r 0).toNat →
      S.mem.readLE (s.sp.toNat - 24) 8 = tInt → S.mem.readLE (s.sp.toNat - 16) 8 = c32Addr →
      (CallOK S 4096 5 ∧ StackRoom S 4096 5 ∧
        ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 S.mem (S.regs 0).toNat (S.regs 1).toNat
          (S.regs 2).toNat (S.regs 3).toNat (S.regs 4).toNat ∧
        ReadsOutside (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (calleeStack S 4096 5) ∧
        ReadsSafe R L (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) ∧
        LiveAt R (Extracted.program.contractAddr "fmt.errorf")
          [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat, (S.regs 3).toNat, (S.regs 4).toNat] L bud
          (errorfCost S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (S.regs 28).toNat S.mem
          (calleeStack S 4096 5)) := by
    intro S hf' hg hsp h30a h30b h0 h1 h2 h3 h4 hbA hbV hA0 hA1 hA2 hA3 hA4 hA5
    have e0 : (S.regs 0).toNat = fmtAddr := by rw [h0]; rfl
    have e1 : (S.regs 1).toNat = 26 := by rw [h1]; rfl
    have e2 : (S.regs 2).toNat = s.sp.toNat - 56 := by rw [h2]; exact hsp56
    have e3 : (S.regs 3).toNat = 3 := by rw [h3]; rfl
    have e4 : (S.regs 4).toNat = 3 := by rw [h4]; rfl
    rw [e0, e1, e2, e3, e4]
    obtain ⟨hargs, hreads, hmsg, hcosteq, hop⟩ := facts S.mem (r 0).toNat hf' hb48 hb0 hbA hbV hA0 hA1 hA2 hA3 hA4 hA5
    have hf2 : MemFrame s.mem S.mem (R.rt ++ ((s.sp.toNat - 4208, s.sp.toNat + 24) :: Ri.priv)) :=
      hf'.mono (by intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h.2.2, h.2.1⟩)
    have hc := call_pre' R L bud (errorfCost S.mem fmtAddr 26 (s.sp.toNat - 56))
      (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, s.sp.toNat - 56, 3, 3] Ri.priv
      (s := s) (S := S) (lo := s.sp.toNat - 4208) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 5) (fr := 112)
      hg1 hg2 (by omega) hgo hcgo hf2 hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega) (by omega) ha4
      (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4208) = 4208 + 24 by omega]; exact hw4) hwrt hwL hok
      (by rw [hg]; exact RtInv.inv_frame hf' hRS hinv) (by rw [hcosteq]; have := hmsgL s.mem; omega)
    refine ⟨hc.1, hc.2.1, hargs, ?_, ?_, hc.2.2⟩
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [calleeStack, outside_cons, outside_nil, and_true]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> omega
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (Outside.of_sub hO2.1 (by omega) (by omega)))
      · exact Or.inr (Or.inl (hRo _ _ (by omega) (by omega)))
      · exact Or.inr (Or.inl heO.1)
      · rcases htO with h | h | h
        · exact Or.inl h
        · simp only [outside_append] at h; exact Or.inr (Or.inl h.1)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl hbO)
      · exact Or.inr (Or.inl (Outside.of_sub hO3.1 (by omega) (by omega)))
  have post_facts : ∀ (M m1 : Memory), MemFrame M m1 (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 8 * 5)]) →
      MemFrame s.mem M (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) →
      M.accessible (r 0).toNat 8 false = true → M.readLE (r 0).toNat 8 = len.toNat →
      M.readLE (s.sp.toNat - 56) 8 = tErr → M.readLE (s.sp.toNat - 48) 8 = e →
      M.readLE (s.sp.toNat - 40) 8 = tInt → M.readLE (s.sp.toNat - 32) 8 = (r 0).toNat →
      M.readLE (s.sp.toNat - 24) 8 = tInt → M.readLE (s.sp.toNat - 16) 8 = c32Addr →
      M.readLE (s.sp.toNat - 120) 8 = s.sp.toNat - 8 → M.readLE (s.sp.toNat - 112) 8 = ret →
      LiveFrame M m1 L [] → ∀ a b : Nat,
      ErrorfPost (Env.mk tErr iErr tInt iWrap) R M fmtAddr 26 (s.sp.toNat - 56)
        [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8), (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 8 * 5)] L bud
        (s.regs 28).toNat a b m1 →
      m1.readLE (s.sp.toNat - 120) 8 = s.sp.toNat - 8 ∧ m1.readLE (s.sp.toNat - 112) 8 = ret ∧
        m1.accessible (s.sp.toNat - 120) 8 false = true ∧ m1.accessible (s.sp.toNat - 112) 8 false = true ∧
        a = iWrap ∧ b + 32 ≤ 2 ^ 48 ∧ m1.accessible b 32 true = true ∧
        m1.readLE (b + 8) 8 = (errMsg (strBytes s.mem tp tl) len.toNat).length ∧
        strBytes m1 (m1.readLE b 8) (errMsg (strBytes s.mem tp tl) len.toNat).length = errMsg (strBytes s.mem tp tl) len.toNat ∧
        m1.readLE (b + 16) 8 = iErr ∧ m1.readLE (b + 24) 8 = e ∧ FreshFrom [(b, b + 32)] L ∧
        InRanges b 32 R.rt ∧ MemFrame s.mem m1 (R.rt ++ (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)])) ∧
        LiveFrame s.mem m1 L [] ∧
        R.inv (bud - (2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48))
          (L ++ ((b, b + 32) :: range0 (m1.readLE b 8) (errMsg (strBytes s.mem tp tl) len.toNat).length))
          (s.regs 28).toNat
          (view R.rt (L ++ ((b, b + 32) :: range0 (m1.readLE b 8) (errMsg (strBytes s.mem tp tl) len.toNat).length)) m1) := by
    intro M m1 hfr hMF hbA hbV hA0 hA1 hA2 hA3 hA4 hA5 h29 h30 hlf a b hp
    obtain ⟨hargs, hreads, hmsgM, hcostM, hopM⟩ := facts M (r 0).toNat hMF hb48 hb0 hbA hbV hA0 hA1 hA2 hA3 hA4 hA5
    obtain ⟨hiw, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hfresh, hinr, hsep1, hsep2, hinv'⟩ := hp
    have hs29 : m1.readLE (s.sp.toNat - 120) 8 = s.sp.toNat - 8 := by
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hRo _ _ (by omega) (by omega), by omega, by omega⟩)]
      exact h29
    have hs30 : m1.readLE (s.sp.toNat - 112) 8 = ret := by
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hRo _ _ (by omega) (by omega), by omega, by omega⟩)]
      exact h30
    have hacc : ∀ a n w, m1.accessible a n w = s.mem.accessible a n w := fun a n w => by
      rw [hfr.accessible, hMF.accessible]
    have hmlen : (msgOf M fmtAddr 26 (s.sp.toNat - 56)).length = (errMsg (strBytes s.mem tp tl) len.toNat).length := by
      rw [hmsgM]
    refine ⟨hs29, hs30, ?_, ?_, hiw, ?_, ?_, ?_, ?_, ?_, ?_, hfresh, hinr, ?_, ?_, ?_⟩
    · rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))
    · rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))
    · simpa [wrapBytes] using hd1
    · exact hd2
    · rw [hmlen] at hd3; exact hd3
    · rw [hmlen, hmsgM] at hd4; exact hd4
    · simp only [wrapErrOffset] at hd6; exact hd6
    · simp only [wrapErrOffset] at hd7; rw [hopM] at hd7; exact hd7
    · exact MemFrame.trans hMF hfr (by frame_sub)
    · exact LiveFrame.trans (LiveFrame.of_win hMF hLS) hlf (fun _ _ h => h)
    · rw [hcostM] at hinv'; rw [hmlen] at hinv'; exact hinv'
  have hm0 : m'.readLE (s.sp.toNat - 56) 8 = tErr := by
    rw [hfr.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hPo _ _ (by omega) (by omega), by omega, by omega⟩)]
    (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega
  have hm1 : m'.readLE (s.sp.toNat - 48) 8 = e := by
    rw [hfr.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hPo _ _ (by omega) (by omega), by omega, by omega⟩)]
    (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega)
  have hm120 : m'.readLE (s.sp.toNat - 120) 8 = s.sp.toNat - 8 := by
    rw [hfr.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hPo _ _ (by omega) (by omega), by omega, by omega⟩)]
    (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega)
  have hm112 : m'.readLE (s.sp.toNat - 112) 8 = ret := by
    rw [hfr.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hPo _ _ (by omega) (by omega), by omega, by omega⟩)]
    (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have h := hret.user; have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega)
  refine Reaches.call (Summary.withExit (hf L bud) hret) rfl
    (key _ (by janus_frame) (by simp [setReg, Map.keepABI]) (by simp [hsp112]; omega) (by simp [setReg, hFA]) (by simp [setReg, hFA])
      (by simp [setReg, hFA]) (by simp [setReg, hFA]) (by simp [setReg, hFA]) (by simp [setReg, hFA]) (by simp [setReg, hFA])
      (by (try dsimp only); simp only [Memory.accessible_writeLE]; exact hbacc)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hbval)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hm0)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hm1)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega) (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by have h := (r 0).isLt; have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega)) (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega) (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega)) ?_
  intro s' hpc' ⟨r2, vr2, fl2, m1, ex1, ep1, hs1, hfr1, hlf1, hpost⟩
  subst hs1
  simp only [calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    hsp112, hsp56] at hfr1 hlf1 hpost
  have hr := post_facts _ _ hfr1 (by janus_frame)
      (by (try dsimp only); simp only [Memory.accessible_writeLE]; exact hbacc)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hbval)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hm0)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hm1)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega) (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by have h := (r 0).isLt; have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega)) (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega) (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self]; try omega)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hm120)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact hm112)
      hlf1 _ _ hpost
  obtain ⟨hs29, hs30, hacc29, hacc30, hiw, hb32, hbacc2, hlen2, hstr2, herr2, hdat2, hfresh2, hinr2, hMf, hLf, hInv⟩ := hr
  have hr0 : r2 0 ≠ 0#64 := fun h => by
    rw [h] at hiw
    exact absurd hiw (by decide)
  janus_run [hs29, hs30, hr0]
  have e29 : BitVec.ofNat 64 (s.sp.toNat - 8) = s.sp - 8#64 := by bv_omega
  refine ⟨e29, ?_⟩
  unfold ErrPost
  refine ⟨by simpa [setReg, Map.keepABI] using hiw, (r2 1).toNat,
    by simp [setReg, Map.keepABI], hb32, hbacc2, hlen2, hstr2, ?_, ?_, hfresh2, hinr2, hMf, hLf, hInv, ?_, ?_⟩
  · rw [herr2]; exact hv2.symm
  · rw [hdat2]; exact hv3.symm
  · exact untouched_read hzU hMf hLf
  · exact untouched_read hdU hMf hLf

def SuccPre (z bp : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true ∧ Ptr32 s.mem bp false ∧
    Disjoint z.toNat 32 bp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
    Disjoint bp.toNat 32 (s.sp.toNat - 120) 144

def SuccPost (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = s.mem.readLE bp.toNat 32 ∧
    MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]

set_option maxHeartbeats 16000000 in
theorem succblk (impl : List Segment) (z bp len cap : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat = 32 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
        SuccPre z bp s ∧ s.regs 29 = s.sp - 8#64)
      (SuccPost z bp len cap) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hl, hlc, hc48, ⟨⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3⟩, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2 hd3
  unfold SuccPost
  janus_run
  refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), ?_, ?_⟩
  · rw [Util.readLE_32 s.mem bp.toNat]
  · janus_frame

def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ s.regs 29 = s.sp - 8#64 ∧
    (len.toNat = 32 → SuccPre z bp s) ∧ (len.toNat ≠ 32 → ErrPre R Ri H L bud e tp tl z bp len cap s)

def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  (len.toNat = 32 → SuccPost z bp len cap s s') ∧ (len.toNat ≠ 32 → ErrPost R Ri L bud e tp tl z bp len cap s s')

set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Segment) (R : RtInv) (Ri : IfaceModel) (hl : Ri.Laws) (H : RtReady)
    (hf : ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R
      tErr iErr tInt iWrap 26 fmtNum 4294967296)
    (hconv : ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H)
    (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp, len, cap]
      (Pre R Ri H L bud e tp tl z bp len cap) (Post R Ri L bud e tp tl z bp len cap) := by
  intro ret hret s hs ⟨hg, hst, hlc, hc48, hfp, hS, hE⟩
  by_cases h : len.toNat ≠ 32
  · have := errblk1 impl R Ri hl H hf hconv L bud e tp tl z bp len cap ret hret s hs ⟨h, hlc, hc48, hfp, hE h⟩
    exact this.mono fun s' ⟨hab, hp⟩ => ⟨hab, fun h32 => absurd h32 h, fun _ => hp⟩
  · have := succblk impl z bp len cap ret hret s hs ⟨hg, hst, by omega, hlc, hc48, hS (by omega), hfp⟩
    exact this.mono fun s' ⟨hab, hp⟩ => ⟨hab, fun _ => hp, fun h32 => absurd h32 h⟩


/-! ## Non-vacuity: every hypothesis of `correctness` holds together (error branch, `len = 300`)

The `fmt.errorf` stub and the `convT64` model code placed at the two contract addresses, the toy runtime with the
constants cell (`errR`), the interface model `R0`, a state in which `ErrBadEncodedLength` holds its link-time image
(`*errors.errorString` itab and the string `"bad ssz encoded length"`), an admissible return address. -/

namespace Witness

open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

abbrev evData : Nat := Extracted.dataAddr.«github.com/holiman/uint256.ErrBadEncodedLength→data»

def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def retA : Nat := 0x1000
def textAddr : Nat := 2 * evData
def txtNum : Nat := 39081144270194845157923351904996902443455527117939042

def dat (a : Nat) : Option Nat :=
  Extracted.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then some (d.bytes.getD (a - d.base) 0) else none

def regions0 : List Region :=
  [⟨sp0 - 4208, 4232, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨ev, evData + 16 - ev, true⟩,
    ⟨textAddr, 0x40, false⟩, ⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩] ++
    Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩

def base : Memory :=
  (((((((((((((((⟨fun _ => 0, regions0⟩ : Memory).writeLE ev 8 iErr).writeLE (ev + 8) 8 evData).writeLE evData 8 textAddr).writeLE
    (evData + 8) 8 22).writeLE textAddr 22 txtNum).writeLE BUMP 8 HEAP).writeLE CELL 8 iErr).writeLE (CELL + 8) 8 iWrap).writeLE
    (g0 + 16) 8 0x1000).writeLE TD 8 8).writeLE (TD + 20) 1 8).writeLE ID 8 8).writeLE (ID + 64) 8 1).writeLE TAB 8 ID).writeLE
    (TAB + 8) 8 TD

def mem0 : Memory := ⟨fun a => match dat a with | some b => BitVec.ofNat 8 b | none => base.bytes a, regions0⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded mem0 := by
  unfold Program.DataLoaded
  decide +kernel

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 0x600000 else if i = 1 then BitVec.ofNat 64 0x700000 else if i = 2 then 300
      else if i = 3 then 512 else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 sp0 - 8#64
      else if i = 30 then BitVec.ofNat 64 retA else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩, mem := mem0 }

abbrev cAddrE : Nat := Extracted.program.contractAddr "fmt.errorf"
abbrev cAddrC : Nat := Extracted.program.contractAddr "runtime.convT64"
def convSeg : Segment := { name := "model", base := cAddrC, words := convT64Code }
def implAt : List Segment := [convSeg, Janus.Contracts.ErrorfRealLive.errorfSeg cAddrE]
def R0e : RtInv := errR [] iErr iWrap (fun _ _ => True)

theorem tysOK : TysOK ([] : Tys) := by intro t ht; simp at ht

theorem hf0 : ErrorfLive (Extracted.program.link implAt) cAddrE 4096 R0e tErr iErr tInt iWrap 26 fmtNum 4294967296 := by
  show ErrorfLive ((Extracted.program.link [convSeg]).link [Janus.Contracts.ErrorfRealLive.errorfSeg cAddrE]) cAddrE 4096 R0e
    tErr iErr tInt iWrap 26 fmtNum 4294967296
  exact Janus.Contracts.ErrorfRealLive.errorf_live_at _ cAddrE [] tysOK tErr tInt iErr iWrap (by decide) (by decide) (by decide)
    (Janus.Contracts.ErrorfRealLive.fetchedAt_link (Extracted.program.link [convSeg]) cAddrE (by decide +kernel)
      (by decide +kernel) (by decide +kernel))

def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem hconv0 : ConvT64 (Extracted.program.link implAt) cAddrC R0 Htrue := by
  rw [linked_eq]
  intro s hpc ⟨hpre, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine rtReturn_of R0 1 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Memory.accessible_writeLE]
      exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (s.mem.writeLE 66304 8 _).readLE 66304 8 = _
      rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 0).isLt

theorem hret0 : RetAddr (Extracted.program.link implAt) retA := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link implAt).withExit retA) Extracted.entry
    [BitVec.ofNat 64 0x600000, BitVec.ofNat 64 0x700000, 300, 512] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000

theorem dat_none (i : Nat) (h : 2000000 ≤ i) : dat i = none := by
  unfold dat
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have hb : ∀ d ∈ Extracted.data, d.base + d.bytes.length ≤ 2000000 := by decide +kernel
  have := hb d hd
  simp only [ite_eq_right_iff]
  intro hc; omega

theorem base_zero (i : Nat) (h : 268435456 ≤ i) : base.bytes i = 0 := by
  unfold base
  repeat rw [Memory.bytes_writeLE_outside]
  all_goals first
    | rfl
    | (simp only [ev, evData, Extracted.dataAddr.«github.com/holiman/uint256.ErrBadEncodedLength»,
        Extracted.dataAddr.«github.com/holiman/uint256.ErrBadEncodedLength→data», textAddr,
        BUMP, HEAP, CELL, g0, TD, ID, TAB]
       omega)

theorem mem0_zero (i : Nat) (h : 268435456 ≤ i) : mem0.bytes i = 0 := by
  unfold mem0
  simp only [dat_none i (by omega)]
  exact base_zero i h

theorem rinv0 (g : Nat) : R0e.inv 176 [] g (view R0e.rt [] mem0) := by
  show errInv [] iErr iWrap 176 [] g (view (errRt []) [] mem0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [view_toy_err]
    refine ⟨HEAP, ?_, by decide, by decide, by decide, by intro r hr; simp at hr, ?_, ?_, ?_, ?_, by intro t ht; simp at ht⟩
    · rw [readLE_view (inRanges_bump []) (by simp [outside_nil])]; decide
    · intro i h1 h2
      rw [readLE_view (inRanges_heap (n := 1) (by simp [HEAP] at *; omega) (by simp [HEND, HEAP, HSIZE] at *; omega)) (by simp [outside_nil])]
      simp only [Memory.readLE, Nat.mul_zero, Nat.add_zero]
      rw [mem0_zero i (by simp [HEAP, HEND, HSIZE] at *; omega)]; rfl
    · decide
    · decide
    · decide
  · rw [readLE_view (inRanges_cell [] (Nat.le_refl _) (by omega)) (by simp [outside_nil])]; decide
  · rw [readLE_view (inRanges_cell [] (by omega) (by omega)) (by simp [outside_nil])]; decide
  · rw [view_accessible]; decide

theorem pre0 : Pre R0e R0 Htrue [] 176 evData textAddr 22 (BitVec.ofNat 64 0x600000) (BitVec.ofNat 64 0x700000) 300 512 s0 := by
  have hrt : R0e.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, rfl,
    fun h => absurd h (by decide), fun _ => ?_⟩
  have hOut : ∀ a n, (a + n ≤ HEAP ∨ HEND ≤ a) → (a + n ≤ BUMP ∨ BUMP + 8 ≤ a) → (a + n ≤ WBUF ∨ WBUF + 64 ≤ a) →
      (a + n ≤ CELL ∨ CELL + 16 ≤ a) → Outside a n R0e.rt := by
    intro a n h1 h2 h3 h4; rw [hrt]; simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3, h4⟩
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_, ?_,
    rinv0 _, by decide, ?_, ?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ErrHolds
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · rw [hrt]; intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · intro r hr; simp at hr
  · show True; trivial
  · intro d hd
    have : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length (R0e.rt ++ R0.priv) := by
      rw [hrt]; simp only [R0_priv, outside_append, outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]
      decide +kernel
    exact this d hd
  · rw [hrt]; simp only [R0_priv, outside_append, outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · rw [hrt]; simp only [R0_priv, outside_append, outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · right; left
    rw [hrt]; simp only [R0_priv, outside_append, outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · refine ⟨?_, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
    · show Env0 s0.mem (s0.regs 28)
      refine ⟨by decide, by decide, ?_⟩
      unfold Desc; decide
    · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
    · unfold Disjoint; decide
    · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · trivial
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · intro r hr; simp only [R0_priv, List.mem_singleton] at hr; subst hr
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · intro r hr; simp at hr
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · decide
  · refine ⟨by decide, Or.inl ?_⟩
    rw [hrt]; simp only [R0_priv, outside_append, outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · refine ⟨by decide, Or.inl ?_⟩
    rw [hrt]; simp only [R0_priv, outside_append, outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide

/-- All hypotheses of `correctness` are satisfiable together, in the error branch (`len = 5 < 32`). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat))
    (bud e tp tl : Nat) (ret : Nat) (s : State) (z bp len cap : BitVec 64),
    Ri.Laws ∧
    ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tErr iErr tInt iWrap 26
      fmtNum 4294967296 ∧
    ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, bp, len, cap] s ∧
    Pre R Ri H L bud e tp tl z bp len cap s ∧ len.toNat ≠ 32 :=
  ⟨implAt, R0e, R0, Htrue, [], 176, evData, textAddr, 22, retA, s0, _, _, 300, 512, R0_laws, hf0, hconv0, hret0, setup, pre0,
    by decide⟩

/-- The guarantee fires: the call returns the wrapped error. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit retA) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R0e R0 [] 176 evData textAddr 22 (BitVec.ofNat 64 0x600000) (BitVec.ofNat 64 0x700000) 300 512 s0 s' :=
  correctness implAt R0e R0 R0_laws Htrue hf0 hconv0 [] 176 evData textAddr 22 (BitVec.ofNat 64 0x600000)
    (BitVec.ofNat 64 0x700000) 300 512 retA hret0 s0 setup pre0

end Witness

end Fv256.Arm64.UnmarshalSSZMain
