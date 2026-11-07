import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.IbsA64
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.ScanSciSpec

/-!
# `(*uint256.Int).scanScientificFromString` (arm64): the summary `sci_summary` (internal to `Scan`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg :=
  SfdCfg.mk Extracted.dataAddr.«io.EOF»
    Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»
    Extracted.dataAddr.«github.com/holiman/uint256.multipliers»
    Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
    Extracted.dataAddr.«go:itab.*strconv.NumError,error»
    Extracted.dataAddr.«go:itab.internal/strconv.Error,error»
    Extracted.dataAddr.«.rodata#9967e7a3»
    Extracted.dataAddr.«strconv.ErrSyntax»
    Extracted.dataAddr.«runtime.writeBarrier»
    Extracted.dataAddr.«.rodata#7233b75a»
    Extracted.dataAddr.«.rodata#575028b4»
    (Extracted.program.contractAddr "runtime.mallocgc")
    (Extracted.program.contractAddr "runtime.memmove")
    (Extracted.program.contractAddr "runtime.newobject")
    (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
    (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

theorem apart_win {z a n lo hi : Nat} (hz : z + 32 ≤ lo ∨ hi ≤ z) (h1 : lo ≤ a) (h2 : a + n ≤ hi) : Apart z 32 a n := by
  unfold Apart; omega

set_option hygiene false in
/-- drop the bulk facts `janus_data` / `janus_run` leave in the context (they make `omega` slow) -/
macro "clr" : tactic => `(tactic| (
  try clear h_data0
  try clear h_data1
  try clear h_data2
  try clear h_data3
  try clear h_data4
  try clear h_data5
  try clear h_data6
  try clear h_data7
  try clear h_data8
  try clear h_data9
  try clear h_data10
  try clear h_data11
  try clear h_data12
  try clear h_data13
  try clear h_data14
  try clear h_data15
  try clear h_data16
  try clear h_data17
  try clear h_data18
  try clear h_data19
  try clear h_data20
  try clear h_data21
  try clear h_data22
  try clear h_data23
  try clear h_data24
  try clear h_data25
  try clear h_data26
  try clear h_data27
  try clear h_data28
  try clear h_data29
  try clear h_data30
  try clear h_ddisj0_0
  try clear h_ddisj0_1
  try clear h_ddisj0_2
  try clear h_ddisj0_3
  try clear h_ddisj0_4
  try clear h_ddisj0_5
  try clear h_ddisj0_6
  try clear h_ddisj0_7
  try clear h_ddisj0_8
  try clear h_ddisj0_9
  try clear h_ddisj0_10
  try clear h_ddisj0_11
  try clear h_ddisj0_12
  try clear h_ddisj0_13
  try clear h_ddisj0_14
  try clear h_ddisj0_15
  try clear h_ddisj0_16
  try clear h_ddisj0_17
  try clear h_ddisj0_18
  try clear h_ddisj0_19
  try clear h_ddisj0_20
  try clear h_ddisj0_21
  try clear h_ddisj0_22
  try clear h_ddisj0_23
  try clear h_ddisj0_24
  try clear h_ddisj0_25
  try clear h_ddisj0_26
  try clear h_ddisj0_27
  try clear h_ddisj0_28
  try clear h_ddisj0_29
  try clear h_ddisj0_30
  try clear h_post0
  try clear h_post1
  try clear h_post2
  try clear h_post3
  try clear h_post4
  try clear h_post5
  try clear h_post6
  try clear h_post7
  try clear h_post8
  try clear h_post9
  try clear h_post10
  try clear h_post11
  try clear h_post12
  try clear h_post13
  try clear h_post14
  try clear h_post15
  try clear h_post16
  try clear h_post17
  try clear h_post18
  try clear h_post19
  try clear h_post20
  try clear h_post21
  try clear h_post22
  try clear h_post23
  try clear h_post24
  try clear h_post25
  try clear h_post26
  try clear h_post27
  try clear h_post28
  try clear h_post29
  try clear h_post30
  try clear h_post31
  try clear h_post32
  try clear h_post33
  try clear h_post34
  try clear h_post35
  try clear h_post36
  try clear h_post37
  try clear h_post38
  try clear h_post39
  try clear h_post40
  try clear h_post41
  try clear h_post42
  try clear h_post43
  skip))

theorem mod64 (v : BitVec 64) : v.toNat % 256 ^ 8 = v.toNat := Nat.mod_eq_of_lt (by have := v.isLt; simpa using this)

theorem pr_frame {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)} {p n : Nat} (hF : MemFrame m m' ws)
    (h : Fv256.IndexByte.PageReadable m p n) : Fv256.IndexByte.PageReadable m' p n := by
  unfold Fv256.IndexByte.PageReadable at *
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by rw [hF.accessible]; exact h.2⟩

theorem ofn (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by simp

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"
abbrev ibsEntry : Nat := segAddr Extracted.program "internal/bytealg.IndexByteString"
abbrev sciEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).scanScientificFromString"

/-- the summary's precondition -/
def Pre0 (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) : Prop :=
  SciPre cfg R R2 T b L lo hi dst pS nS s ∧ InitDone cfg R2 s.mem ∧
    Extracted.program.DataLoaded s.mem

/-- what every state `S` of the body after the prologue satisfies, relative to the entry state `s0` -/
def Fr (lo : Nat) (dst pS nS : BitVec 64) (s0 S : State) : Prop :=
  S.sp = s0.sp - 112#64 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 18 = s0.regs 18 ∧ S.regs 29 = s0.sp - 120#64 ∧
  MemFrame s0.mem S.mem [(lo, s0.sp.toNat - 8), (s0.sp.toNat + 8, s0.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] ∧
  S.mem.regions = s0.mem.regions ∧
  S.mem.readLE (s0.sp.toNat - 112) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 120) 8 = (s0.regs 29).toNat ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = dst.toNat ∧ S.mem.readLE (s0.sp.toNat + 16) 8 = pS.toNat ∧
  S.mem.readLE (s0.sp.toNat + 24) 8 = nS.toNat

theorem str_outside {pS nS lo hi dst sp : Nat} (hPW : nS = 0 ∨ pS + nS ≤ lo ∨ hi ≤ pS)
    (hPZ : nS = 0 ∨ pS + nS ≤ dst ∨ dst + 32 ≤ pS) (hlo : lo ≤ sp) (hhi : sp + 32 ≤ hi) (k : Nat) (hk : k < nS) :
    Outside (pS + k) 1 [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem indexOfNat_congr (b b' : Nat → Nat) (n c : Nat) (h : ∀ k, k < n → b k = b' k) :
    Fv256.IndexByte.indexOfNat b n c = Fv256.IndexByte.indexOfNat b' n c := by
  unfold Fv256.IndexByte.indexOfNat
  rw [find_congr (fun i => b i == c % 256) (fun i => b' i == c % 256) _ (fun x hx => by simp only [h x (List.mem_range.1 hx)])]

theorem seg_post_ibs (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0) (S : State) (hfr : Fr lo dst pS nS s S)
    (hpc : S.pc = BitVec.ofNat 64 (sciEntry + 0x44)) (h30 : S.regs 30 = BitVec.ofNat 64 (sciEntry + 0x44))
    (hx0 : (S.regs 0).toNat = Fv256.IndexByte.indexOfNat (bytesAt s.mem pS.toNat) nS.toNat 101) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hEnv0 := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv0
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hfr
  have hSsp : S.sp.toNat = s.sp.toNat - 112 := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hr136 : S.mem.readLE (S.sp.toNat + 136) 8 = nS.toNat := by rw [hSsp, show s.sp.toNat - 112 + 136 = s.sp.toNat + 24 by omega]; exact fn
  have hr128 : S.mem.readLE (S.sp.toNat + 128) 8 = pS.toNat := by rw [hSsp, show s.sp.toNat - 112 + 128 = s.sp.toNat + 16 by omega]; exact fp
  have hr120 : S.mem.readLE (S.sp.toNat + 120) 8 = dst.toNat := by rw [hSsp, show s.sp.toNat - 112 + 120 = s.sp.toNat + 8 by omega]; exact fdst
  have hrfp : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [hSsp, show s.sp.toNat - 112 - 8 = s.sp.toNat - 120 by omega]; exact ffp
  have hrlr : S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by rw [hSsp]; exact fra
  have hacc : S.mem.accessible (S.sp.toNat - 8) 152 true = true := by
    rw [fmf.accessible]
    exact Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x44 = 754100 from by rw [h_sci]] at hpc h30
  have hx0e : (S.regs 0).toNat = (match Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat with | some i => i | none => 2 ^ 64 - 1) := by
    rw [hx0]; exact indexOf_eq_idxE _ _
  have hSal : S.sp.toNat % 16 = 0 := by omega
  clear fsp
  have h28' : S.regs 28 = s.regs 28 := f28
  by_cases hnone : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = none
  · rw [hnone] at hx0e
    have hx : S.regs 0 = 18446744073709551615#64 := BitVec.eq_of_toNat_eq (by simpa using hx0e)
    have e1 : (addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true := by decide
    janus_run [e1, hpc, hx, hr136, hr128, hr120, hacc, hrfp, hrlr, h28', h30, f28, hSal] until [sfdEntry]
    case h =>
      have hF : MemFrame s.mem S.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
        fmf.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      refine ReachesRet.call (Summary.regions (hsfd b L lo (S.sp.toNat + 32) dst pS nS)) (by first | rfl | decide) ?_ ?_
      · refine call_pre cfg htop hF hSal (by omega) (Or.inl rfl) (by omega) (Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩) hP48
          (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
          (by simp [setReg_apply, f28]) (by simp; omega) (by simp) hzR hzPr hzS hzg (by rw [fmf.accessible]; exact hzP.1) hzP.2
      · intro S3 hpc3 ⟨hpost, hreg3⟩
        obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hpost
        dsimp only at k1 k2 k3 k4 k5 k6 hcases
        have hra : S3.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by rw [k6]; exact hrlr
        have hfp' : S3.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [k5]; exact hrfp
        have hsi : (S.sp.toNat + 112) = s.sp.toNat := by rw [hSsp]; exact Nat.sub_add_cancel (Nat.le_trans (by omega) hlo)
        have hacc3 : S3.mem.accessible (S.sp.toNat - 8) 152 true = true := by
          have e : S3.mem.regions = S.mem.regions := hreg3
          unfold Janus.Arm64.Memory.accessible at hacc ⊢
          rw [e]; exact hacc
        have hacc3' : S3.mem.accessible (S.sp.toNat - 8) 8 false = true :=
          Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inl rfl) (by omega) (by omega)
        janus_run [hra, hfp', hSal, ofn, hacc3, hacc3']
        have hsp112 : S.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := s.sp.isLt; omega)
        have hbytes : decParse (bytesAt s.mem pS.toNat) nS.toNat = decParse (bytesAt S.mem pS.toNat) nS.toNat :=
          Fv256.I.decParse_congr _ _ _ (fun k hk => (fmf.readLE (pS.toNat + k) 1 (str_outside hPW hPZ (by omega) hhi k hk)).symm)
        have hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = decParse (bytesAt S.mem pS.toNat) nS.toNat := by
          rw [sci_none hn hnone, hbytes]
        have hlift : ∀ (rs : List (Nat × Nat)) (ws1 : List (Nat × Nat)), MemFrame S.mem S3.mem ws1 →
            (∀ a n, Outside a n rs → Outside a n ws1 ∧ Outside a n [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) →
            MemFrame s.mem S3.mem rs := fun rs ws1 h2 hout => fmf.trans h2 (fun a n ho => by
              have := hout a n ho; exact ⟨this.2, this.1⟩)
        unfold SciPost
        have hSs : S.sp.toNat + 112 = s.sp.toNat := hsi
        have hr28' : S3.regs 28 = s.regs 28 := by rw [k3, ← f28]; simp [setReg_apply]
        have hr18' : S3.regs 18 = s.regs 18 := by rw [k4, ← f18]; simp [setReg_apply]
        rcases hcases with ⟨v, hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c1, cTe, cMF⟩
        · have hM3 := hlift [(lo, hi), (dst.toNat, dst.toNat + 32)] _ cMF (fun a n h => out_ok h (by omega) hhi hSs)
          refine ⟨hsp112, by simp [setReg_apply], by simp [setReg_apply, hr28'], by simp [setReg_apply, hr18'],
            hM3.readLE _ _ ?_, hM3.readLE _ _ ?_, Or.inl ⟨v, ?_, by simpa [setReg_apply] using c0, by simpa [setReg_apply] using c1, ?_, hM3⟩⟩
          · sorry
          · sorry
          · rw [hsci]; exact hv
          · sorry
        all_goals sorry
  · sorry

theorem seg_entry (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hibs : Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 sciEntry) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18⟩ := hEnv'
  have hacc : s.mem.accessible (s.sp.toNat - 120) 152 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  janus_eval_nat h_sci : sciEntry
  rw [h_sci] at hpc
  janus_run [hpc, h0, h1, h2, hacc, hr8, hr7, hr4, Nat.mod_eq_of_lt (show (s.regs 28).toNat + 16 < 2 ^ 64 by omega)] until [ibsEntry]
  case hq =>
    -- nS = 0 : `dst` cleared
    have hn0 : nS.toNat = 0 := by janus_assumption
    have hdst : Apart dst.toNat 32 (s.sp.toNat - 120) 152 := apart_win hzW (by omega) (by omega)
    clr
    unfold SciPost
    simp only [hn0, sci_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨0, rfl, ?_, ?_, ?_, ?_⟩⟩
    · trivial
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp (disch := omega) only [val256, Fv256.Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    · sorry
  case h =>
    clr
    refine ReachesRet.call (Summary.regions (hibs pS nS 101)) (by first | rfl | decide) ?_ ?_
    · refine ⟨by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], ?_⟩
      exact pr_frame (ws := [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) (by janus_frame) hpage
    · intro S2 hpc2 ⟨⟨hx0, hmem, hsp, h18, h28, h29, h30⟩, hreg⟩
      dsimp only at hpc2 hx0 hmem hsp h18 h28 h29 h30 hreg
      have hfr : Fr lo dst pS nS s S2 := by
        unfold Fr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsp]
        · rw [h28]; simp [setReg_apply]
        · rw [h18]; simp [setReg_apply]
        · rw [h29]; simp [setReg_apply]
        · rw [hmem]; janus_frame
        · rw [hreg]; simp
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
      have hbytes : ∀ k, k < nS.toNat → Fv256.IndexByte.bytesOf (S2.mem) pS.toNat k = bytesAt s.mem pS.toNat k := by
        intro k hk
        have := hfr.2.2.2.2.1.readLE (pS.toNat + k) 1 (str_outside hPW hPZ (by omega) hhi k hk)
        exact this
      rw [← hmem] at hx0
      have hx0' : (S2.regs 0).toNat = Fv256.IndexByte.indexOfNat (bytesAt s.mem pS.toNat) nS.toNat 101 := by
        rw [hx0]
        exact indexOfNat_congr _ _ _ _ hbytes
      have hbrn : ¬ nS.toNat = 0 := by janus_assumption
      refine seg_post_ibs impl R R2 T b L lo hi dst pS nS hsfd s ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ (by intro h; exact hbrn h) S2 hfr ?_ ?_ hx0'
      · rw [hpc2]; sorry
      · rw [h30]; sorry

end Fv256.Arm64.ScanSci
