# generates lean/Fv256/Arm64/FormatFastPF.lean (P and F call sites) and FormatFastB.lean (branch segments)
HDR = """import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast
"""
OB = "obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre"
sites = [
 # name, start, ret, tabword, fnvar, nargs, args, R
 ("p", 0x60, 0x70, "ht20", "fP", 1, "(BitVec.ofNat 64 fP) (S.regs 2) (S.regs 3)", "RP", "hfP"),
 ("f1", 0x7c, 0x90, "ht18", "fF", 2, "(BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 3)", "RF", "hfF"),
 ("f2", 0x9c, 0xb0, "ht18", "fF", 2, "(BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 3)", "RF", "hfF"),
 ("f3", 0xbc, 0xd0, "ht18", "fF", 2, "(BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 3)", "RF", "hfF"),
 ("f4", 0xe0, 0xf4, "ht18", "fF", 2, "(BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 3)", "RF", "hfF"),
 ("f5", 0x100, 0x114, "ht18", "fF", 2, "(BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 3)", "RF", "hfF"),
]
out = HDR
for (n, st, rt_, tw, fn, na, args, R, hf) in sites:
    out += f"""
/-- site `{n}`: call through the itab, return at `Format+{hex(rt_)}` -/
theorem {n}_call (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) ({R} : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) {fn} {na} stack 120 rt (fun _ => []) {R} (fun _ => True))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + {hex(st)}))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + {hex(rt_)})) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧
        ∃ j0 j1 j2, {R} data {args} j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  {OB}
  simp only [CodePtrOK] at {hf}
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, {tw}, hta, hwa, i4] until [Extracted.entry + {hex(rt_)}] calls [hC]
  rename_i junk f v m ex ep hk1 hk2 hR
  janus_grab MemFrame as hfr
  refine ReachesRet.done ?_ ⟨?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]
"""
out += "\nend Fv256.Arm64.FormatFast\n"
open('/srv/fv-uint256-wf3/lean/Fv256/Arm64/FormatFastPF.lean','w').write(out)
