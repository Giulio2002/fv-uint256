HDR = """import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast
"""
OB = "obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre"
BIG = 0x204
sites = [("w",0x5c,0x60,1,1,"big"),("p",0x70,0x7c,1,2,"cont"),("f1",0x90,0x9c,0,2,"cont"),("f2",0xb0,0xbc,0,2,"cont"),
         ("f3",0xd0,0xe0,0,3,"cont"),("f4",0xf4,0x100,0,2,"cont"),("f5",0x114,0x11c,0,4,"big")]
out = HDR
for (n, ret, cont, reg, tk, taken) in sites:
    for kind in ("cont","big"):
        tgt = cont if kind=="cont" else BIG
        zero = (kind=="cont")
        hbty = f"(S.regs {reg}).toNat % 2 = 0" if zero else f"(S.regs {reg}).toNat % 2 ≠ 0"
        x = f"S.regs {reg}"
        T = {1:f"(BitVec.getLsbD ({x}) 0 == true) = true", 2:f"(BitVec.getLsbD ({x}) 0 == false) = true",
             3:f"(BitVec.getLsbD ({x} ^^^ 1#64) 0 == true) = true", 4:f"(BitVec.getLsbD ({x} ^^^ 1#64) 0 == false) = true"}[tk]
        L = {1:"lsb0_iff",2:"lsb0_false",3:"lsb0_xor",4:"lsb0_xor_false"}[tk]
        if kind == taken:
            hb2 = f"have hb' : {T} := ({L} _).2 (by omega)"
        else:
            hb2 = f"have hb' : ¬ ({T}) := fun h => by have := ({L} _).1 h; omega"
        out += f"""
theorem {n}_{kind} (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + {hex(ret)}))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : {hbty}) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + {hex(tgt)})) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  {hb2}
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  {OB}
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + {hex(tgt)}]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)
"""
out += "\nend Fv256.Arm64.FormatFast\n"
open('/srv/fv-uint256-wf3/lean/Fv256/Arm64/FormatFastB.lean','w').write(out)
