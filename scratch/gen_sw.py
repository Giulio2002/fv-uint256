HDR = """import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast
"""
OB = "obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre"
FIN = "exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)"
def lemma(name, tgt, hyps, doc, body_run):
    return f"""
/-- the verb switch at `Format+0x11c`: {doc} -/
theorem {name} (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x11c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hlt : ch32 < 2 ^ 32) {hyps} :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + {tgt})) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  {OB}
{body_run}
"""
out = HDR + """
theorem sext_trunc (v : Nat) (hv : v < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (if v % 4294967296 < 2147483648 then v % 4294967296 else v % 4294967296 + 18446744069414584320))).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split <;> omega
"""
out += lemma("sw_dec","0x144","(hch : ch32 = 100 ∨ ch32 = 115 ∨ ch32 = 118)","`d`, `s`, `v` to the `Dec` path",
f"""  rcases hch with h | h | h
  all_goals (janus_run [i112, hwa, i4, h, addSub, addWithCarry, BitVec.msb_eq_decide, sext_trunc ch32 hlt] until [Extracted.entry + 0x144]
             {FIN})""")
out += lemma("sw_hex","0x19c","(hch : ch32 = 120)","`x` to the `Hex` path",
f"""  janus_run [i112, hwa, i4, hch, addSub, addWithCarry, BitVec.msb_eq_decide, sext_trunc ch32 hlt] until [Extracted.entry + 0x19c]
  {FIN}""")
out += lemma("sw_big","0x204","(h1 : ch32 ≠ 100) (h2 : ch32 ≠ 115) (h3 : ch32 ≠ 118) (h4 : ch32 ≠ 120)","any other verb to the big path",
f"""  janus_run [i112, hwa, i4, addSub, addWithCarry, BitVec.msb_eq_decide, sext_trunc ch32 hlt] until [Extracted.entry + 0x204]
  all_goals {FIN}""")
out += "\nend Fv256.Arm64.FormatFast\n"
open('/srv/fv-uint256-wf3/lean/Fv256/Arm64/FormatFastSw.lean','w').write(out)
