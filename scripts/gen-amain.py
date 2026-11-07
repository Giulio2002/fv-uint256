#!/usr/bin/env python3
# generate amd64 *Main.lean (+ *Hsfd.lean discharge stubs) from the conditional theorems
import re
D='/srv/fv-uint256-wJ/lean/Fv256/Amd64/'
# name, namespace-of-cond, extra imports, witness module + cores, has hhex
funcs={
 'UnmarshalText':dict(ns='Fv256.Amd64.UnmarshalText',hex=True,cfgns='Fv256.Amd64.UnmarshalTextS',wit='AUtWitC'),
 'UnmarshalJSON':dict(ns='Fv256.Amd64.UnmarshalJSON',hex=True,cfgns='Fv256.Amd64.UnmarshalTextS',wit='AUjWitC'),
 'FromDecimal':dict(ns='Fv256.Amd64.FromDecimal',hex=False,cfgns='Fv256.Amd64.FromDecimal',wit='AFdWitC'),
 'MustFromDecimal':dict(ns='Fv256.Amd64.MustFromDecimal',hex=False,cfgns='Fv256.Amd64.MustFromDecimal',wit='AMFdWitC'),
}
for f,d in funcs.items():
    src=open(D+f+'.lean').read()
    i=src.index('theorem correctness_cond')
    j=src.index(':= by',i)
    sig=src[i:j]
    pre=src[:i]
    sig=sig.replace('theorem correctness_cond','theorem correctness')
    # remove hsfd binder and hhex binder
    sig=re.sub(r"    \(hsfd : .*?SfdSummary [^\n]*?nS'\)","",sig,flags=re.S)
    sig=re.sub(r"    \(hhex : [^\n]*\n","",sig)
    cm='    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)\n      (Extracted.program.contractAddr "runtime.cmpstring") 16)'
    if '\n    : Ensures' in sig: sig=sig.replace('\n    : Ensures',"\n"+cm+'\n    : Ensures',1)
    else: sig=re.sub(r"\s*:\n    (Ensures)","\n"+cm.replace("\\","\\\\")+" :\n    \\1",sig,count=1)
    open('/tmp/sig_%s.txt'%f,'w').write(sig)
    print(f, 'hsfd' in sig, 'hhex' in sig, 'hcmp' in sig)

# ---------------- second stage: write the Main and Hsfd files
wits={
 'UnmarshalText':('Fv256.Amd64.UtWit',[('nonvacuous','nonvacuous_core'),('hex','hex_core')]),
 'UnmarshalJSON':('Fv256.Amd64.UjWit',[('nonvacuous','nonvacuous_core'),('unquoted','unq_core')]),
 'FromDecimal':('Fv256.Amd64.FdWit',[('nonvacuous','nonvacuous_core')]),
 'MustFromDecimal':('Fv256.Amd64.MFdWit',[('nonvacuous','nonvacuous_core')]),
}
SFD="""∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary @CFG@ (Extracted.program.link impl) @ENTRY@ R R2 T b' L' lo' hi' z pS' nS'"""
for f,d in funcs.items():
    src=open(D+f+'.lean').read()
    sig=open('/tmp/sig_%s.txt'%f).read()
    opens=[l for l in src.split('namespace')[0].split('\n') if l.startswith('open ')]
    ns=d['ns']; mk=f+'Main'; hs=f+'Hsfd'
    cfg=d['cfgns']+'.cfg'; entry=d['cfgns']+'.sfdEntry'
    if f=='UnmarshalJSON': cfg=ns+'.cfg'; entry=ns+'.sfdEntry'
    pan = f=='MustFromDecimal'
    # Hsfd stub
    hsfd=f"""import Extracted
import {ns}
@HEXIMP@
/-!
# `{f}` (amd64): the `SetFromDecimal` summary `hsfd` from the library lemma (discharge, one small lemma per function)

PENDING: `Fv256.Amd64.SfdLib.hsfd_of_link` (FV-I5, planned statement in /srv/fv-uint256-wi/NOTES-I.md).
-/

{chr(10).join(opens)}

namespace Fv256.Amd64.{hs}

theorem hsfd (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T : Nat)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    {SFD.replace('@CFG@',cfg).replace('@ENTRY@',entry)} := by
  sorry -- PENDING hsfd_of_link

end Fv256.Amd64.{hs}
"""
    hsfd=hsfd.replace('@HEXIMP@','')
    open(D+hs+'.lean','w').write(hsfd)
    # Main
    wns,cores=wits[f]
    args=('P ' if pan else '')+'impl R R2 T b L lo hi '+('z pI nI cI' if d['hex'] else 'pS nS')+' hif hnew hmg hmv hwb1 hwb2'+(' hsb (Fv256.Amd64.UnmarshalHexDisch.hhex_of impl)' if d['hex'] else '')
    hsf=f"(Fv256.Amd64.{hs}.hsfd impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp)"
    main=f"""import Extracted
import {ns}
import Fv256.Amd64.{hs}
{'import Fv256.Amd64.UnmarshalHexDisch' if d['hex'] else ''}
import Fv256.Amd64.{d['wit']}

/-!
# `{f}` (amd64): the Extracted-level theorem (`hhex`/`hsfd` discharged) and its non-vacuity witnesses
-/

{chr(10).join(opens)}

open {ns}

namespace Fv256.Amd64.{mk}

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
{sig}:= by
  exact {ns}.correctness_cond {args} {hsf}

namespace Witness
"""
    w=open(D+d['wit']+'.lean').read()
    for nm,core in cores:
        a=w.index('theorem '+core+' :'); b=w.index(':=\n  ⟨impl',a)
        st=w[a:b].replace('theorem '+core+' :','theorem '+nm+' :')
        st=re.sub(r'\bcfg\b',cfg,st)
        st=st.replace('pinPanicRuntime',wns+'.pinPanicRuntime')
        main+=f"\nset_option maxRecDepth 100000 in\n{st}:= {wns}.{core}\n"
    main+=f"\nend Witness\n\nend Fv256.Amd64.{mk}\n"
    open(D+mk+'.lean','w').write(main)
