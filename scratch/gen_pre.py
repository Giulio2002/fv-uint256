HDR = """import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.FormatFastSites
import Fv256.Arm64.FormatFastSw

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast
"""
CH = "((S0.regs 3).toNat % 2 ^ 32)"
FIN = f"FInv rt stack z tab data {CH} S0"
BIGMEM = "(List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))"
# steps: (site name, R var, hypothesis name, XRes expression builder)
steps = [
 ("p","RP","hP","PRes RP data fP (fun j => j.toNat % 2 = 0)"),
 ("f1","RF","hF","FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)"),
 ("f2","RF","hF","FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)"),
 ("f3","RF","hF","FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)"),
 ("f4","RF","hF","FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)"),
 ("f5","RF","hF","FRes RF data fF 0x23 (fun j => j.toNat % 2 = 0)")]
# XResNot (for the non-plain disjunct)
def xnot(n):
    return {"p":"PRes RP data fP (fun j => j.toNat % 2 ≠ 0)","f1":"FRes RF data fF 0x2b (fun j => j.toNat % 2 ≠ 0)",
            "f2":"FRes RF data fF 0x20 (fun j => j.toNat % 2 ≠ 0)","f3":"FRes RF data fF 0x2d (fun j => j.toNat % 2 ≠ 0)",
            "f4":"FRes RF data fF 0x30 (fun j => j.toNat % 2 ≠ 0)","f5":"FRes RF data fF 0x23 (fun j => j.toNat % 2 ≠ 0)"}[n]
def xproof(n):
    # proof of XRes from hR (RP/RF with S.regs 2/3 args) and hb
    if n=="p":
        return "⟨_, _, j0, j1, j2, hR, hb⟩"
    return "⟨_, j0, j1, j2, hR, hb⟩"
def xproof_not(n):
    return xproof(n)
def disj(i, total, proof):
    # i-th disjunct (0-based) of total
    s = proof
    if i < total-1:
        s = f"Or.inl ({s})" if False else s
    return s
def orwrap(i, total, inner):
    # position i in an n-ary right-nested Or of `total` disjuncts
    out = inner
    if i < total-1:
        out = f"Or.inl ({out})"
    for _ in range(i):
        out = f"Or.inr ({out})"
    return out

out = HDR
out += f"""
theorem pre_fast (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW RP RF : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True))
    (hP : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True))
    (hF : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True))
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) :
    RT (Extracted.program.link impl) S0
      [(Extracted.entry + 0x144, fun S => {FIN} S ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
          ({CH} = 100 ∨ {CH} = 115 ∨ {CH} = 118)),
       (Extracted.entry + 0x19c, fun S => {FIN} S ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧ {CH} = 120),
       (Extracted.entry + 0x204, fun S => {FIN} S ∧
          NotPlain RW RP RF data fW fP fF (S0.regs 3) {CH})] := by
  have hlt : {CH} < 2 ^ 32 := Nat.mod_lt _ (by decide)
  refine RT.trans (w_site impl rt stack fW fP fF fWr RW z tab data hW S0 hpc hpre) ?_
  intro t ht S1 hr1 hq1
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · obtain ⟨hi1, -, j0, j1w, j2, hR1, hb1⟩ := hq1
    have hH1 : WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0 := ⟨⟨j0, j2, hR1⟩, hb1⟩
"""
# nested chain
hist = "(WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0)"
indent = "    "
total = 8
for idx,(n,R,hh,xres) in enumerate(steps):
    k = idx+1  # state index of the entry
    hn = f"hH{k}"
    out += f"""{indent}refine RT.trans ({n}_site impl rt stack fW fP fF fWr {R} z tab data {CH} _ {hn} {hh} S0 S{k} hr{k} hpre hi{k}) ?_
{indent}intro t ht S{k+1} hr{k+1} hq{k+1}
{indent}simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
{indent}rcases ht with rfl | rfl
{indent}· obtain ⟨hi{k+1}, hHa, j0, j1, j2, hR, hb⟩ := hq{k+1}
{indent}  have hH{k+1} : ({hist} ∧ {xres}) := ⟨hHa, {xproof(n)}⟩
"""
    # the big exit comes after the rest of the chain; we collect it
    indent_in = indent + "  "
    # remember to emit the big-exit branch later: store
    steps[idx] = (n,R,hh,xres,hist,indent,k)
    hist = f"({hist} ∧ {xres})"
    indent = indent_in
# after f5: hist = full PlainHist-shaped
k = 7
out += f"""{indent}have hpl : ∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1 := ⟨_, j1w, hH7⟩
{indent}by_cases hdec : {CH} = 100 ∨ {CH} = 115 ∨ {CH} = 118
{indent}· have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x144)) S7
{indent}      (fun S => {FIN} S ∧ (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
{indent}        ({CH} = 100 ∨ {CH} = 115 ∨ {CH} = 118)) :=
{indent}    rr_mono (sw_dec impl rt stack fW fP fF fWr z tab data {CH} S0 S7 hr7 hpre hi7 hlt hdec) (fun S h => ⟨h, hpl, hdec⟩)
{indent}  refine RT.widen (RT.of_reachesRet k) ?_
{indent}  intro t ht; simp only [List.mem_singleton] at ht; subst ht
{indent}  exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
{indent}· by_cases hhex : {CH} = 120
{indent}  · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x19c)) S7
{indent}        (fun S => {FIN} S ∧ (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧ {CH} = 120) :=
{indent}      rr_mono (sw_hex impl rt stack fW fP fF fWr z tab data {CH} S0 S7 hr7 hpre hi7 hlt hhex) (fun S h => ⟨h, hpl, hhex⟩)
{indent}    refine RT.widen (RT.of_reachesRet k) ?_
{indent}    intro t ht; simp only [List.mem_singleton] at ht; subst ht
{indent}    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩
{indent}  · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S7
{indent}        (fun S => {FIN} S ∧ NotPlain RW RP RF data fW fP fF (S0.regs 3) {CH}) :=
{indent}      rr_mono (sw_big impl rt stack fW fP fF fWr z tab data {CH} S0 S7 hr7 hpre hi7 hlt (fun h => hdec (Or.inl h))
{indent}        (fun h => hdec (Or.inr (Or.inl h))) (fun h => hdec (Or.inr (Or.inr h))) hhex)
{indent}        (fun S h => ⟨h, {orwrap(7,8,"⟨j1w, hH7, fun h => hdec (Or.inl h), fun h => hdec (Or.inr (Or.inl h)), fun h => hdec (Or.inr (Or.inr h)), hhex⟩")}⟩)
{indent}    refine RT.widen (RT.of_reachesRet k) ?_
{indent}    intro t ht; simp only [List.mem_singleton] at ht; subst ht
{indent}    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl, fun _ h => h⟩
"""
# big exits, innermost first in reverse order
for (n,R,hh,xres,hist_k,ind,k) in reversed(steps):
    dis = orwrap(k, 8, f"⟨j1w, {hist_k}, {xproof_not(n)}⟩") if False else None
    # the disjunct index of step n: p -> 1, f1 -> 2, ... f5 -> 6
    di = {"p":1,"f1":2,"f2":3,"f3":4,"f4":5,"f5":6}[n]
    out += f"""{ind}· obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq{k+1}
{ind}  exact RT.here (Extracted.entry + 0x204, _) {BIGMEM} hr{k+1} ⟨hib, {orwrap(di, 8, f"⟨j1w, hHb, {xproof_not(n)}⟩")}⟩
"""
out += f"""  · obtain ⟨hib, -, j0, j1, j2, hRb, hbb⟩ := hq1
    exact RT.here (Extracted.entry + 0x204, _) {BIGMEM} hr1 ⟨hib, {orwrap(0,8,"⟨j1, ⟨j0, j2, hRb⟩, hbb⟩")}⟩

end Fv256.Arm64.FormatFast
"""
open('/srv/fv-uint256-wf3/lean/Fv256/Arm64/FormatFastPre.lean','w').write(out)
