import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SpecScan
import Fv256.Proofs.Common.IndexByteSpec
import Fv256.Proofs.Common.IbsA64
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC
import Fv256.Proofs.Arm64.ScanSciSpec
import Fv256.Spec.Arm64.ScanSciBase

/-!
# `(*uint256.Int).scanScientificFromString` (arm64): the summary `sci_summary` (internal to `Scan`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

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

theorem indexOfNat_congr (b b' : Nat → Nat) (n c : Nat) (h : ∀ k, k < n → b k = b' k) :
    Fv256.IndexByte.indexOfNat b n c = Fv256.IndexByte.indexOfNat b' n c := by
  unfold Fv256.IndexByte.indexOfNat
  rw [find_congr (fun i => b i == c % 256) (fun i => b' i == c % 256) _ (fun x hx => by simp only [h x (List.mem_range.1 hx)])]


abbrev errBigAddr : Nat := Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»

theorem cfg_errBig : SfdCfg.errBig cfg = errBigAddr := rfl

theorem hitab_ne : BitVec.ofNat 64 cfg.numErrItab ≠ 0 := by
  unfold cfg
  decide

abbrev expEntry : Nat := 0xbd2a0
abbrev moEntry : Nat := 0xbadb0

/-- the `SetFromDecimal` summary at every window -/
def HSfd (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T : Nat) : Prop :=
  ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS'

/-- the `Exp` summary -/
def HExp (impl : List Janus.Segment) : Prop :=
  Summary (Extracted.program.link impl) expEntry (ExpPre Extracted.program.DataLoaded) ExpPost

/-- the `MulOverflow` summary (as `Ensures.toSummaryIn` gives it) -/
def HMo (impl : List Janus.Segment) : Prop :=
  ∀ z x y : BitVec 64, Summary (Extracted.program.link impl) moEntry
    (fun s => RetAddr Fv256.Arm64.MulOverflowProg.program (s.regs regLR).toNat ∧ ArgsFrom s 0 [z, x, y] ∧ MoPreS z x y s)
    (MoPostS z x y)

end Fv256.Arm64.ScanSci
