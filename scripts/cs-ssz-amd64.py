#!/usr/bin/env python3
"""cs-ssz-amd64.py [FN...] : MarshalSSZIntoMain / UnmarshalSSZMain amd64: ConvT64 (ConvT64Site) + fmt.errorf (ErrorfLiveSite) call sites (error-branch witness)."""
import subprocess, sys
CFG = {'MarshalSSZIntoMain': dict(LEN=5, BUD=138, TL=21), 'UnmarshalSSZMain': dict(LEN=300, BUD=176, TL=22)}
BLOCK = '''/-- The call state of `runtime.convT64` (U-WITNESS-CALLSITE): `convT64(len)` at its entry, `RSP = sp0 - 112`, memory of `s0`. -/
def csCv0 : State := { s0 with regs := fun i => if i = 0 then {LEN} else if i = 4 then BitVec.ofNat 64 (sp0 - 112) else s0.regs i }
def csCv : State := { csCv0 with rip := BitVec.ofNat 64 cAddrC }

theorem csCv_rip : csCv.rip = BitVec.ofNat 64 cAddrC := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csCv_pre : ConvT64Site R0 Htrue csCv := by
  refine ⟨⟨⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩, trivial⟩
  · unfold Desc; decide
  · simp only [R0_priv, R0_depth, outside_cons, outside_nil, and_true]; decide

/-- The memory of the `fmt.errorf` call: the `[]any` `{{*errorString, ErrBad..}, {int, &len}, {int, &32}}` at `sp0 - 56` and the box of `len` at `BOX`. -/
def memE : Arm64.Memory :=
  ((((((mem0.writeLE (sp0 - 56) 8 tErr).writeLE (sp0 - 48) 8 evData).writeLE (sp0 - 40) 8 tInt).writeLE (sp0 - 32) 8 BOX).writeLE
    (sp0 - 24) 8 tInt).writeLE (sp0 - 16) 8 c32Addr).writeLE BOX 8 {LEN}
def csEr0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 fmtAddr else if i = 3 then 26 else if i = 1 then BitVec.ofNat 64 (sp0 - 56)
    else if i = 7 then 3 else if i = 6 then 3 else if i = 4 then BitVec.ofNat 64 (sp0 - 104) else s0.regs i, mem := memE }
/-- The call state of `fmt.errorf` (U-WITNESS-CALLSITE): `Errorf(fmt, []any{err, len, 32})` at its entry, `RSP = sp0 - 104`. -/
def csEr : State := { csEr0 with rip := BitVec.ofNat 64 cAddrE }

theorem csEr_rip : csEr.rip = BitVec.ofNat 64 cAddrE := rfl

theorem csEr_frame : MemFrame mem0 memE [(sp0 - 4200, sp0 + 24), (BOX, BOX + 8)] := by
  unfold memE
  have h1 : (sp0 - 4200, sp0 + 24) ∈ [(sp0 - 4200, sp0 + 24), (BOX, BOX + 8)] := by simp
  have h2 : (BOX, BOX + 8) ∈ [(sp0 - 4200, sp0 + 24), (BOX, BOX + 8)] := by simp
  exact ((((((MemFrame.refl _ _).writeLE _ h1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)).writeLE _ h1
    (by simp only [sp0]; omega) (by simp only [sp0]; omega)).writeLE _ h1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)).writeLE _ h1
    (by simp only [sp0]; omega) (by simp only [sp0]; omega)).writeLE _ h1 (by simp only [sp0]; omega) (by simp only [sp0]; omega)).writeLE _ h1
    (by simp only [sp0]; omega) (by simp only [sp0]; omega)).writeLE _ h2 (by simp only [BOX]; omega) (by simp only [BOX]; omega)

theorem csEr_view : view R0e.rt [] memE = view R0e.rt [] mem0 := by
  have hrt : R0e.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  have hO1 : Outside (sp0 - 4200) 4224 R0e.rt := by
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  have hO2 : Outside BOX 8 R0e.rt := by
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, BOX, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  rw [view_nil, view_nil]
  refine Janus.Contracts.Stack.rtView_eq_of_frame csEr_frame rfl (fun a ha => ?_)
  have d1 := InRanges.disjoint ha hO1
  have d2 := InRanges.disjoint ha hO2
  simp only [outside_cons, outside_nil]
  refine ⟨?_, ?_, trivial⟩ <;> omega

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csEr_pre : ErrorfLiveSite R0e cAddrE 4096 tErr iErr tInt iWrap 26 fmtNum 4294967296 [] {BUD} csEr := by
  have hrt : R0e.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  have hrd : Janus.Contracts.Errorf.errorfReads csEr.mem (csEr.regs 0).toNat (csEr.regs 3).toNat (csEr.regs 1).toNat =
      [(fmtAddr, 26), (sp0 - 56, 48), (evData, 16), (textAddr, {TL}), (BOX, 8), (c32Addr, 8)] := by decide
  refine ⟨by decide, by decide, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩, ?_, ?_, ?_,
    ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · unfold Janus.Contracts.Errorf.ArgsOK; simp only [Readable]; decide
  · unfold ReadsOutside; rw [hrd]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [liveWin64, calleeStack64, outside_append, outside_cons, outside_nil]; decide)
  · unfold Janus.Contracts.Errorf.ReadsSafe; rw [hrd]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (Or.inl (by rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide))
  · show R0e.ok cAddrE [(csEr.regs 0).toNat, (csEr.regs 3).toNat, (csEr.regs 1).toNat, (csEr.regs 7).toNat, (csEr.regs 6).toNat]
    decide
  · show R0e.inv {BUD} [] (csEr.regs 14).toNat (view R0e.rt [] memE)
    rw [csEr_view]; exact rinv0 _
  · intro r hr
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide)

'''
for fn, c in CFG.items():
    if len(sys.argv) > 1 and fn not in sys.argv[1:]: continue
    f = f'lean/Fv256/Amd64/{fn}.lean'
    s = open(f).read()
    if 'import Fv256.Amd64.CallSites.Live' not in s:
        s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
    open(f, 'w').write(s)
    bf = f'/tmp/cs-{fn}.lean'
    open(bf, 'w').write(BLOCK.replace('{LEN}', str(c['LEN'])).replace('{BUD}', str(c['BUD'])).replace('{TL}', str(c['TL'])))
    rp = lambda a: f'∃ s_c : State, s_c.rip = BitVec.ofNat 64 {a} ∧ '
    CV = 'cAddrC'; ER = 'cAddrE'
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf, '--block-name', fn,
      '--conj', rp(CV) + 'Fv256.CallSites.ConvT64Site Ri H s_c', '--proof', '⟨csCv, csCv_rip, csCv_pre⟩',
      '--conj', rp(ER) + f'Fv256.CallSites.ErrorfLiveSite R {ER} 4096 tErr iErr tInt iWrap 26 fmtNum 4294967296 [] {c["BUD"]} s_c', '--proof', '⟨csEr, csEr_rip, csEr_pre⟩'],
      capture_output=True, text=True)
    print(fn, r.stdout.strip(), r.stderr.strip()[-300:])
