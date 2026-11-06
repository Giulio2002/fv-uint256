import sys,os,re
isa=sys.argv[1]   # arm64 | amd64
ARM = isa=='arm64'
D='Arm64' if ARM else 'Amd64'
L='/srv/fv-uint256-wd/lean/Fv256/'+D
os.makedirs(L+'/SbCases',exist_ok=True)
# ---- reuse the monolithic generator for statement pieces/closers by loading its source ----
src=open('/srv/fv-uint256-wd/wip-d/gen_sb_%s.py'%('arm' if ARM else 'amd')).read()
B,A=88,(72 if ARM else 24)
def sub_len(txt,k):  # statement text with len := k#64
    return txt.replace('len.toNat','(BitVec.ofNat 64 %d).toNat'%k)
if ARM:
    PRE=f"""GuardOK s 48 ∧ StackOK s {B} {A} ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
        Disjoint z.toNat 32 (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) ∧
        Disjoint z.toNat 32 (s.sp.toNat - {B}) {B+A} ∧
        Disjoint (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) (s.sp.toNat - {B}) {B+A} ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - {B}) {B+A}"""
    POST=f"""s'.regs 0 = z ∧
        val256 s'.mem z.toNat =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - {B}) {B+A}"""
    HEAD="""open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec"""
    INTRO="""  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3, hdg⟩
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hdg
"""
    RUN="janus_run"
else:
    PRE=f"""StackGuardOK s 48 ∧ StackWritable s {B} {A} ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Buffer s z 32 true ∧ Buffer s ptr len.toNat false ∧
        (z.toNat + 32 ≤ ptr.toNat + len.toNat - used len.toNat ∨ ptr.toNat + len.toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - {B} ∨ (s.regs regSP).toNat + {A} ≤ z.toNat) ∧
        (ptr.toNat + len.toNat ≤ (s.regs regSP).toNat - {B} ∨ (s.regs regSP).toNat + {A} ≤ ptr.toNat + len.toNat - used len.toNat) ∧
        ((s.regs 14).toNat + 16 + 8 ≤ (s.regs regSP).toNat - {B} ∨ (s.regs regSP).toNat + {A} ≤ (s.regs 14).toNat + 16)"""
    POST=f"""s'.regs 0 = z ∧
        valueAt s' z 32 =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - {B}) {B+A}"""
    HEAD="""open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic"""
    INTRO="""  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hd, hlc, hc48, ⟨hzw, hz⟩, ⟨hpw, hp⟩, hd1, hd2, hd3, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hd2 hd3 hdg
  janus64_data hd [hacc]
  simp only [valueAt]
"""
    RUN="janus64_run [Util.readLE_32]"
# closers: exec the closer() function from the monolithic generator
ns={}
mode='full'
m=re.search(r"def closer\(k\):.*?(?=\nbody)",src,re.S)
if ARM: code="mode='full'\nB,A=88,72\n"+m.group(0)
else: code="mode='full'\nB,A,G=88,24,48\nBV0=%r\nZ=%r\now=%r\n"%(re.search(r'^BV0="(.*)"$',src,re.M).group(1),re.search(r'^Z="(.*)"$',src,re.M).group(1),re.search(r"^ow='(.*)'$",src,re.M).group(1))+m.group(0)
exec(code,ns); closer=ns['closer']
def case_text(k):
    big = k==32
    nm='caseBig' if big else f'case{k}'
    if big:
        pre,post=PRE,POST
        args='(z ptr len cap : BitVec 64) (h32 : 32 ≤ len.toNat)'
        lenarg='len'
    else:
        pre,post=sub_len(PRE,k),sub_len(POST,k)
        args='(z ptr cap : BitVec 64)'
        lenarg=f'BitVec.ofNat 64 {k}'
    if ARM:
        if big:
            pre_steps="  simp only [Disjoint, used, if_neg (show ¬ len.toNat < 32 by omega)] at hd1 hd2 hd3 ⊢\n"
        else:
            pre_steps="  simp only [Disjoint, used, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT, ite_true, Nat.add_sub_cancel] at hd1 hd2 hd3 hp ⊢\n"
    else:
        if big:
            pre_steps="  have hu : used len.toNat = 32 := by simp [used]; omega\n  rw [hu] at hd1 hd3 ⊢\n"
        else:
            pre_steps=f"  have hu : used (BitVec.ofNat 64 {k}).toNat = {k} := by simp [used]\n  rw [hu] at hd1 hd3 ⊢\n  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_sub_cancel] at hd1 hd2 hd3 hp\n"
    cl=closer(k)
    ind=lambda t: ''.join('  '+l+'\n' if l.strip() else '\n' for l in t.split('\n')[:-1]) if t.endswith('\n') else '  '+t
    return f"""import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.{D}.SetBytesDefs

{HEAD}

namespace Fv256.{D}.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem {nm} {args} :
    Ensures Extracted.program Extracted.entry [z, ptr, {lenarg}, cap]
      (fun s => {pre})
      (fun s s' => {post}) := by
{ind(INTRO)}{ind(pre_steps)}    {RUN}
{cl}

end Fv256.{D}.SetBytes
"""
open(L+'/SetBytesDefs.lean','w').write(f"""import Extracted

namespace Fv256.{D}.SetBytes

/-- number of bytes used: all of them up to 32, else the last 32 -/
def used (len : Nat) : Nat := if len < 32 then len else 32

end Fv256.{D}.SetBytes
""")
for k in range(33):
    open(L+f'/SbCases/Case{"Big" if k==32 else k}.lean','w').write(case_text(k).replace(f"import Fv256.{D}.SetBytesDefs",f"import Fv256.{D}.SetBytesDefs"))
# ---- main file: take the monolithic file's header and witness ----
mono=open(L+'/SetBytes.lean').read()
if 'SbCases' in mono: sys.exit('already split; regenerate monolith first')
open(L+'/SetBytes.mono.bak','w').write(mono)
w=mono.index('\nnamespace Witness')
witness=mono[w:mono.index('\nend Fv256.%s.SetBytes\n'%D)]
hdr_end=mono.index('/-- number of bytes used')
header=mono[:hdr_end]
header=header.replace('import Fv256.Util\n','import Fv256.Util\nimport Fv256.%s.SetBytesDefs\n'%D+''.join(f'import Fv256.{D}.SbCases.Case{k}\n' for k in range(32))+f'import Fv256.{D}.SbCases.CaseBig\n',1)
cs=' ∨ '.join(f'len.toNat = {k}' for k in range(32))+' ∨ 32 ≤ len.toNat'
main=f"""set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => {PRE})
      (fun s s' => {POST}) := by
  intro ret hret s hs hpre
  rcases (show {cs} by omega) with {' | '.join(f'h{k}' for k in range(32))} | hbig
"""
for k in range(32):
    main+=f"""  · have hl : len = BitVec.ofNat 64 {k} := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case{k} z ptr cap ret hret s hs hpre
"""
main+="  · exact caseBig z ptr len cap hbig ret hret s hs hpre\n"
open(L+'/SetBytes.lean','w').write(header+main+witness+f"\nend Fv256.{D}.SetBytes\n")
