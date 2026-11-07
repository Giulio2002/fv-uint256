HDR = """import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast
"""
out = HDR
for (name, start, kind) in [("wrd_call",0x15c,"`d/v/s`"),("wrh_call",0x1c8,"`x`")]:
    out += f"""
/-- the `Write` call of the {kind} path (`Format+{hex(start)}`: after `stringtoslicebyte`; the slice is `(x0, x1, x2) = (ptr, len, cap)`),
the epilogue and the return -/
theorem {name} (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RWr : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (bs : List Nat) (ptr len cap : Nat)
    (hWr : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr (FastWP data bs))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + {hex(start)}))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h0 : S.regs 0 = BitVec.ofNat 64 ptr) (h1 : S.regs 1 = BitVec.ofNat 64 len) (h2 : S.regs 2 = BitVec.ofNat 64 cap)
    (hlen : len = bs.length) (hstr : Janus.Spec.strBytes S.mem ptr len = bs) (hbd : ptr + len ≤ 2 ^ 48)
    (hacc : 0 < len → S.mem.accessible ptr len false = true) (hcap : len ≤ cap) (hcap64 : cap < 2 ^ 64)
    (hdis : ptr + len ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ ptr) (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S
      (fun S' => S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
        S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
        MemFrame S0.mem S'.mem (FL rt S0.sp.toNat stack) ∧
        (∃ j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2)) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0', h1', h2', h29', hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfWr hret
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  have hr0 : S.mem.readLE S0.sp.toNat 8 = S0.mem.readLE S0.sp.toNat 8 :=
    ifr.readLE _ _ (out_fl_save (hout.of_sub (by omega) (by omega)) (by omega) (by omega) hst)
  have hr8 : S.mem.readLE (S0.sp.toNat - 8) 8 = S0.mem.readLE (S0.sp.toNat - 8) 8 :=
    ifr.readLE _ _ (out_fl_save (hout.of_sub (by omega) (by omega)) (by omega) (by omega) hst)
  janus_run [i96, i104, ht30, hta, hwa, hr0, hr8, h0, h1, h2, i4, hstr, hbd, hacc] calls [hWr]
  rename_i junk f v m ex ep hk1 hk2 hR hb1
  have hfr : MemFrame S.mem m (rt ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 8 + 32)]) := by
    first | exact hk1 | exact hk2
  exact ⟨frame_call ifr (by omega) hfr, _, _, _, hR⟩
"""
out += "\nend Fv256.Arm64.FormatFast\n"
open('/srv/fv-uint256-wf3/lean/Fv256/Arm64/FormatFastWr.lean','w').write(out)
