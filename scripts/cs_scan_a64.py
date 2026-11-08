#!/usr/bin/env python3
"""cs_scan_a64.py (FV-CSA2 fork C2): call-site conjuncts for arm64 Scan (5 witnesses share one set of 8 call states in ScanWitC)."""
import re, subprocess, sys
sys.path.insert(0, 'scripts')
from cs_unm_a64 import okpos, A, CALLOK, GUARD, GI, SEP2, SEP1, CS_OUT
SB = 'Extracted.program.contractAddr "runtime.slicebytetostring"'
ST = 'Extracted.dataAddr.«runtime.staticuint64s»'
BLOCK = f'''
/-! ### Call-site states (U-WITNESS-CALLSITE), shared by the five `Scan` witnesses: the call state `st 0#64 0#64` with `PC` at each runtime
stub's entry and the argument registers of a request the toy runtime `R` serves; live set `[]`, budget `0x400`. -/
-- CALLSITE-BLOCK
def csB : State := st 0#64 0#64
def csNew : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject"), regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else csB.regs i }}
def csW1 : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }}
def csW2 : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }}
def csMg : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc"), regs := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 0 else csB.regs i }}
def csMv : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove"), regs := fun i => if i = 0 then BitVec.ofNat 64 0xFD000 else if i = 1 then BitVec.ofNat 64 strW else if i = 2 then 1 else csB.regs i }}
def csCm : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring"), regs := fun i => if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 0 else csB.regs i }}
def csIf : State := {{ csB with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq"), regs := fun i => if i = 0 then 0 else csB.regs i }}
def csSb : State := {{ csB with pc := BitVec.ofNat 64 ({SB}), regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 hdrW else if i = 2 then 48 else csB.regs i }}

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R {A('runtime.newobject')} 4096 [] 0x400 csNew := by
  refine ⟨⟨{CALLOK}, typeOK_of (by decide) (by decide), by decide⟩, ⟨{GUARD}, {CS_OUT}⟩,
    ?_, inv0 0#64 0#64, by decide, liveSep_nil _, {SEP2}⟩
  rw [addr_new]; exact {okpos(0, 6, '⟨rfl, Or.inl (by decide)⟩')}

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R {A('runtime.gcWriteBarrier1')} 4096 1 [] 0x400 csW1 := by
  refine ⟨{CALLOK}, ?_, inv0 0#64 0#64, liveSep_nil _, {SEP1}⟩
  rw [addr_w1]; exact {okpos(1, 6, '⟨rfl, rfl⟩')}

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R {A('runtime.gcWriteBarrier2')} 4096 2 [] 0x400 csW2 := by
  refine ⟨{CALLOK}, ?_, inv0 0#64 0#64, liveSep_nil _, {SEP1}⟩
  rw [addr_w2]; exact {okpos(2, 6, '⟨rfl, rfl⟩')}

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R {A('runtime.mallocgc')} 4096 [] 0x400 csMg := by
  refine ⟨⟨{CALLOK}, by decide, Or.inl (by decide)⟩, ⟨{GUARD}, {CS_OUT}⟩,
    ?_, inv0 0#64 0#64, by decide, liveSep_nil _, {SEP2}⟩
  rw [addr_mg]; exact {okpos(3, 6, '⟨rfl, 1, by decide, by decide, by decide⟩')}

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R {A('runtime.memmove')} 4096 [] 0x400 csMv := by
  refine ⟨⟨{GI}, {CALLOK}, {CS_OUT}⟩, ⟨?_, inv0 0#64 0#64, liveSep_nil _, {SEP2}⟩,
    ⟨by decide, by decide, {CS_OUT}⟩, ⟨by decide, by decide, {CS_OUT}, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩⟩
  rw [addr_mv]; exact {okpos(4, 6, '⟨rfl, 0xFD000, strW, 1, by decide, by decide, by decide⟩')}

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 csCm :=
  ⟨{CALLOK}, Or.inl (by decide), Or.inl (by decide)⟩

theorem r3env : (R3 TW).Env csB.mem (csB.regs 28) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := env0 0#64 0#64
  exact h

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite (R3 TW) csIf := by
  refine ⟨⟨r3env, {GI}, {CALLOK}, ?_⟩, fun h => absurd (by decide) h⟩
  simp only [R3_priv, R3_depth, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre 4096 R (slicebytetostringSpec {ST}) slicebytetostringLive ({SB}) [] 0x400 csSb := by
  have hok : R.ok ({SB}) (argWords csSb 3) := by
    rw [addr_sb]
    exact {okpos(5, 6, '⟨rfl, 0, hdrW, by decide⟩')}
  unfold RtLivePre
  refine ⟨{CALLOK}, ?_, ?_, trivial, ⟨{GUARD}, {CS_OUT}⟩, hok, inv0 0#64 0#64, by decide, liveSep_nil _, {SEP2}⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), by decide, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside, calleeStack, outside_cons, outside_nil]
    decide

'''
def conj():
    pc = lambda x: f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {A(x)} ∧ '
    return [
      (pc('runtime.newobject') + f'NewobjectLiveSite R {A("runtime.newobject")} 4096 L b s_c', '⟨Fv256.Arm64.Scan.Witness.csNew, rfl, Fv256.Arm64.Scan.Witness.csNew_pre⟩'),
      (pc('runtime.mallocgc') + f'MallocgcLiveSite R {A("runtime.mallocgc")} 4096 L b s_c', '⟨Fv256.Arm64.Scan.Witness.csMg, rfl, Fv256.Arm64.Scan.Witness.csMg_pre⟩'),
      (pc('runtime.memmove') + f'MemmoveLiveSite R {A("runtime.memmove")} 4096 L b s_c', '⟨Fv256.Arm64.Scan.Witness.csMv, rfl, Fv256.Arm64.Scan.Witness.csMv_pre⟩'),
      (pc('runtime.gcWriteBarrier1') + f'WbLiveSite R {A("runtime.gcWriteBarrier1")} 4096 1 L b s_c', '⟨Fv256.Arm64.Scan.Witness.csW1, rfl, Fv256.Arm64.Scan.Witness.csW1_pre⟩'),
      (pc('runtime.gcWriteBarrier2') + f'WbLiveSite R {A("runtime.gcWriteBarrier2")} 4096 2 L b s_c', '⟨Fv256.Arm64.Scan.Witness.csW2, rfl, Fv256.Arm64.Scan.Witness.csW2_pre⟩'),
      (pc('runtime.cmpstring') + 'Janus.Contracts.Cmpstring.CmpstringPre 16 s_c', '⟨Fv256.Arm64.Scan.Witness.csCm, rfl, Fv256.Arm64.Scan.Witness.csCm_pre⟩'),
      (pc('runtime.ifaceeq') + 'IfaceeqSite R2 s_c', '⟨Fv256.Arm64.Scan.Witness.csIf, rfl, Fv256.Arm64.Scan.Witness.csIf_pre⟩'),
      (f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b s_c', '⟨Fv256.Arm64.Scan.Witness.csSb, rfl, Fv256.Arm64.Scan.Witness.csSb_pre⟩'),
    ]

wc = 'lean/Fv256/Arm64/ScanWitC.lean'
s = open(wc).read()
if 'CALLSITE-BLOCK' not in s:
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    s = s.replace('namespace Fv256.Arm64.Scan.Witness\n', 'open Fv256.Arm64.CallSites\n\nnamespace Fv256.Arm64.Scan.Witness\n', 1)
    i = s.index('/-- The statement of the witness theorem `Scan.Witness.nonvacuous`')
    s = s[:i] + BLOCK.lstrip('\n') + s[i:]
    open(wc, 'w').write(s)
f = 'lean/Fv256/Arm64/Scan.lean'
t = open(f).read()
if 'CallSites.Base' not in t:
    t = t.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    t = t.replace('namespace Fv256.Arm64.Scan\n\nnamespace Witness', 'open Fv256.Arm64.CallSites\n\nnamespace Fv256.Arm64.Scan\n\nnamespace Witness', 1)
    open(f, 'w').write(t)
cj = conj()
for k in range(5):
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--nth', str(k)] +
        sum([['--conj', c, '--proof', p] for c, p in cj], []), capture_output=True, text=True)
    print(k, r.stdout.strip(), r.stderr.strip()[-300:])
