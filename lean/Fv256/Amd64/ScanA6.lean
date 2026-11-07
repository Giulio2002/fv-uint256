import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanIbsCall
import Fv256.Amd64.ScanSfd
import Fv256.Amd64.ScanSfd2
import Fv256.Amd64.ScanIdx
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA


theorem decParse_zero (b : Nat → Nat) : decParse b 0 = .eof := by
  have h : startPos b 0 = 0 := by
    unfold startPos plusEnd zerosFrom
    simp
  unfold decParse
  rw [h]; simp [fromDec]

section tail
variable (b : Nat → Nat) (n i v : Nat) (hn : n ≠ 0) (hi : idxE b n = some i) (hr : decParse b i = .ok v)
  (hnn : ¬ (n - (i + 1) = 1 ∧ b (i + 1) = 48))
include hn hi hr hnn

theorem sci_tail_eof (h : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = .eof) : sciParse b n = .eof := by
  rw [Fv256.Amd64.ScanIdx.sciParse_some_ok b n i v hn hi hr, h]; simp only [hnn, ↓reduceIte, Res.eof]

theorem sci_tail_range (h : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = .range) : sciParse b n = .range := by
  rw [Fv256.Amd64.ScanIdx.sciParse_some_ok b n i v hn hi hr, h]; simp only [hnn, ↓reduceIte]

theorem sci_tail_syn (l m : Nat) (h : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = .syntax l m) :
    sciParse b n = .syntax (i + 1 + l) m := by
  rw [Fv256.Amd64.ScanIdx.sciParse_some_ok b n i v hn hi hr, h]; simp only [hnn, ↓reduceIte]; rfl

theorem sci_tail_ok (e : Nat) (h : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = .ok e) :
    sciParse b n = if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e) := by
  rw [Fv256.Amd64.ScanIdx.sciParse_some_ok b n i v hn hi hr, h]; simp only [hnn, ↓reduceIte]; rfl

end tail

/-- the state `S5` at `sci + 0x129` (after the exponent `SetFromDecimal(&exp, ..)` returned nil): the exponent value is in the local `Int`
at `sp - 40` -/
def Inv5 (P : Janus.Amd64.Program) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst p n : BitVec 64) (i v e : Nat) (s S5 : State) : Prop :=
  S5.regs 4 = s.regs 4 - 112#64 ∧ S5.regs 5 = s.regs 4 - 8#64 ∧ S5.regs 14 = s.regs 14 ∧ S5.xmm 15 = 0 ∧ S5.df = s.df ∧
  S5.fsBase = s.fsBase ∧ MemFrame s.mem S5.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] ∧
  Env cfg R R2 T b L lo ((s.regs 4).toNat - 88) S5 ∧
  S5.mem.readLE ((s.regs 4).toNat - 80) 8 = i ∧ S5.mem.readLE ((s.regs 4).toNat + 8) 8 = dst.toNat ∧
  S5.mem.readLE ((s.regs 4).toNat + 16) 8 = p.toNat ∧ S5.mem.readLE ((s.regs 4).toNat + 24) 8 = n.toNat ∧
  S5.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
  S5.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  idxE (bytesAt s.mem p.toNat) n.toNat = some i ∧ i < n.toNat ∧ decParse (bytesAt s.mem p.toNat) i = .ok v ∧
  ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48) ∧
  decParse (fun k => bytesAt s.mem p.toNat (i + 1 + k)) (n.toNat - (i + 1)) = .ok e ∧
  Janus.Spec.val256 S5.mem dst.toNat = v ∧ Janus.Spec.val256 S5.mem ((s.regs 4).toNat - 40) = e ∧ P.DataLoaded S5.mem

set_option maxRecDepth 100000 in
/-- segments 6-7: the range test on the exponent, `Exp`, `MulOverflow` -/
theorem sci_after2 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v e : Nat) (s S5 : State) (hpc : S5.rip = BitVec.ofNat 64 (sci + 0x129))
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv5 Extracted.program R R2 T b L lo hi dst p n i v e s S5) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S5 (SciPost cfg R R2 b L lo hi dst p n s) := by
  sorry

end Fv256.Amd64.ScanA
