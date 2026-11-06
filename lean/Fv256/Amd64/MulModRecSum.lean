import Fv256.MulModRecProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.CodeIn
import Fv256.UmulProg
import Fv256.ModProg
import Fv256.ChainProg
import Fv256.ReduceProg
import Fv256.Amd64.UmulSum
import Fv256.Amd64.ModSum
import Fv256.Amd64.UdivremL
import Fv256.Amd64.ReduceSpec
import Fv256.Arm64.MulModLem
import Fv256.Amd64.MulModLemA
import Fv256.FieldTac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModRecSum

abbrev mulmodrecEntry : Nat := segAddr Fv256.MulModRecProg.program "github.com/holiman/uint256.(*Int).MulModWithReciprocal"

set_option maxRecDepth 100000 in
theorem hcUmulProg : Janus.Contracts.EqHashModel.CodeIn64 Fv256.UmulProg.program Fv256.MulModRecProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Fv256.MulModRecProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.MulModRecProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcR4 : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ReduceProg.program Fv256.MulModRecProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem mulmodrec_summary (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) :
    Summary Fv256.MulModRecProg.program mulmodrecEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x2f0 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x298 ∧ StackWritable s 0x2e8 0x30 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧ Buffer s (s.regs 7) 32 false ∧ Buffer s (s.regs 6) 40 false ∧
        Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 3).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 1).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 7).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 6).toNat 40 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        (s.mem.readLE ((s.regs 7).toNat + 24) 8 ≠ 0 →
          Fv256.F.RecipWeak (s.mem.readLE (s.regs 7).toNat 32) (s.mem.readLE (s.regs 6).toNat 40)) ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x2e8) 0x318)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 3).toNat 32)
          (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 7).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x2e8, (s.regs 4).toNat),
          ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x30)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, ⟨huw, hu⟩, hdz, hdx, hdy, hdm, hdu, hmu, hdg⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hdu hsp
  have hmu2 : Arm64.Memory.readLE s.mem ((s.regs 7).toNat + 24) 8 ≠ 0 →
      Fv256.F.RecipWeak (Arm64.Memory.readLE s.mem (s.regs 7).toNat 8 + 2 ^ 64 * Arm64.Memory.readLE s.mem ((s.regs 7).toNat + 8) 8 +
        2 ^ 128 * Arm64.Memory.readLE s.mem ((s.regs 7).toNat + 16) 8 + 2 ^ 192 * Arm64.Memory.readLE s.mem ((s.regs 7).toNat + 24) 8) (Arm64.Memory.readLE s.mem (s.regs 6).toNat 40) := by
    intro hd
    have := hmu hd
    rw [Util.readLE_32] at this
    exact this
  janus64_run [hmu2, Fv256.Amd64.MulModLemA.copy40x, Fv256.Arm64.MulModLem.ge192, Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero4, Fv256.F.wv_zero4', false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcUmulProg Fv256.Amd64.UmulSum.umul_summary,
    Fv256.CodeIn.lib_summary hcMod Fv256.Amd64.ModSum.mod_summary,
    Fv256.CodeIn.lib_summary hcChain (Fv256.Amd64.UdivremL.udivrem_rem_L (L := 8) (by omega)),
    Fv256.CodeIn.lib_summary hcR4 hR4]
  · refine ⟨?_, ?_⟩
    · simp [Fv256.F.mulmodSpec]
    · janus_frame
  · refine ⟨?_, ?_⟩
    · simp_all [Fv256.F.mulmodSpec]
    · janus_frame
  · refine ⟨?_, ?_⟩
    · simp_all [Fv256.F.mulmodSpec]
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Amd64.MulModLemA.tail_modA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by janus_assumption) (by janus_assumption)
        (by janus_assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Arm64.MulModLem.tail_udiv _ _ _ _ _ _ _ _ _ _ _ _ _ (Fv256.Amd64.MulModLemA.nz3A _ _ _ _ (by janus_assumption) (by janus_assumption))
        (by janus_assumption) (by janus_assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · janus_frame
  · refine ⟨?_, ?_⟩
    · exact Fv256.Arm64.MulModLem.tail_r4 _ _ _ _ _ _ (Fv256.Arm64.MulModLem.nz4 _ _ _ _ (by janus_assumption))
        (by janus_assumption) (by janus_assumption)
    · janus_frame


theorem mulmodrec_small (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) :
    Summary Fv256.MulModRecProg.program mulmodrecEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x2f0 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x298 ∧ StackWritable s 0x2e8 0x30 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧ Buffer s (s.regs 7) 32 false ∧ Buffer s (s.regs 6) 40 false ∧
        Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 3).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 1).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 7).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 6).toNat 40 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        s.mem.readLE ((s.regs 7).toNat + 24) 8 = 0 ∧
                Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x2e8) 0x318)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 3).toNat 32)
          (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 7).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x2e8, (s.regs 4).toNat),
          ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x30)]) :=
  fun s hpc hp => mulmodrec_summary hR4 s hpc (by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hp
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, fun h => absurd c16 h, c17⟩)

theorem mulmodrec_big (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) :
    Summary Fv256.MulModRecProg.program mulmodrecEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x2f0 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x298 ∧ StackWritable s 0x2e8 0x30 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧ Buffer s (s.regs 7) 32 false ∧ Buffer s (s.regs 6) 40 false ∧
        Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 3).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 1).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 7).toNat 32 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        Apart (s.regs 6).toNat 40 ((s.regs 4).toNat - 0x2e8) 0x318 ∧
        s.mem.readLE ((s.regs 7).toNat + 24) 8 ≠ 0 ∧ Fv256.F.RecipWeak (s.mem.readLE (s.regs 7).toNat 32) (s.mem.readLE (s.regs 6).toNat 40) ∧
                Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x2e8) 0x318)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 3).toNat 32)
          (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 7).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x2e8, (s.regs 4).toNat),
          ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x30)]) :=
  fun s hpc hp => mulmodrec_summary hR4 s hpc (by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := hp
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, fun _ => c17, c18⟩)

end Fv256.Amd64.MulModRecSum
