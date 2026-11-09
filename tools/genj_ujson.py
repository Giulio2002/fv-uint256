ut=open('lean/Fv256/Proofs/Amd64/UnmarshalText.lean').read()
j=open('lean/Fv256/Proofs/Amd64/UnmarshalJSON.lean').read()
head=j[:j.index("set_option maxRecDepth")]
a=ut.index("theorem br_a"); b=ut.index("theorem br_x")
bra=ut[a:b]
sigend=bra.index(" := by\n  intro ret hret s hs hpre")
sig=bra[len("theorem br_a"):sigend]
prelude=bra[sigend+len(" := by\n"):bra.index("  janus64_run until [sfdEntry] calls [hsb]")]
body=bra[bra.index("  janus64_run until [sfdEntry] calls [hsb]"):bra.index("\nset_option maxRecDepth")]
prelude=prelude.replace("- 104 - 4096","- 80 - 4096").replace("- 104 ≤ pI","- 80 ≤ pI").replace("- 104 + 8 ","- 80 + 8 ")
DEC="""(∀ v, decParse (bytesAt s.mem %(p)s) %(n)s = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem %(p)s) %(n)s = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem %(p)s) %(n)s = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem %(p)s) %(n)s = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab)"""
HEX="""(∀ v, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))"""
sub={'p':'(pI.toNat + 1)','n':'(nI.toNat - 2)'}; whole={'p':'pI.toNat','n':'nI.toNat'}
newpost="      (fun s s' =>\n        (Quoted s.mem pI.toNat nI.toNat →\n          (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →\n            "+HEX+") ∧\n          (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →\n            "+(DEC%sub)+")) ∧\n        (¬ Quoted s.mem pI.toNat nI.toNat →\n          "+(DEC%whole)+") ∧\n        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]))"
sigstmt=sig[:sig.index("      (fun s s' =>")]
PRE="(fun s => (PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s ∧ Extracted.program.DataLoaded s.mem) ∧ (nI.toNat : Int) < 2)"
assert PRE in sigstmt
N="(nI.toNat : Int) < 2"; B0="s.mem.readLE pI.toNat 1 = 34"; LW="BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (s.mem.readLE (nI.toNat + pI.toNat - 1) 1)))) - 34#8 = 0#8"
conds={'a':(N,'hc1',"not_q_short (by janus_assumption)"),
 'c':("¬ %s ∧ %s ∧ ¬ (%s)"%(N,B0,LW),'hc1, hc2, hc3',"not_q_last (by janus_assumption)"),
 'd':("¬ %s ∧ ¬ (%s)"%(N,B0),'hc1, hc2',"not_q_b0 (by janus_assumption)")}
oldtail="""    refine ⟨fun hh => ?_, fun _ => ⟨fun v h => ?_, heof, hrange, hsyn⟩, hFr⟩
    · exact absurd hh (not_hex_short (by janus_assumption))
    · obtain ⟨c0, c3, c4⟩ := hok v h
      exact ⟨by simp [c0], by simp [c3], c4⟩"""
assert oldtail in body
out=head
opts="set_option maxRecDepth 100000 in\nset_option maxHeartbeats 16000000 in\n"
for cn in ['a','c','d']:
    cond,pat,lem=conds[cn]
    s2=sigstmt.replace(PRE,"(fun s => (PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s ∧ Extracted.program.DataLoaded s.mem) ∧ "+cond+")")
    pl=prelude.replace("obtain ⟨⟨hpreU, henv, hdl⟩, hc1⟩ := hpre","obtain ⟨⟨hpreU, henv, hdl⟩, "+pat+"⟩ := hpre")
    bd=body.replace(oldtail,"""    refine ⟨fun hh => absurd hh (%s), fun _ => ⟨fun v h => ?_, heof, hrange, hsyn⟩, hFr⟩
    obtain ⟨c0, c3, c4⟩ := hok v h
    exact ⟨by simp [c0], by simp [c3], c4⟩""" % lem)
    if cn=='c':
        lines=bd.rstrip().split("\n")
        ind=["    "+l[2:] if i==0 else "  "+l for i,l in enumerate(lines)]
        ind[0]="  · "+lines[0][2:]
        bd=("  janus64_run until [Extracted.entry + 0x2d, Extracted.entry + 0x4d] calls [hsb]\n"
            "  · exact absurd (by janus_assumption) hc3\n"+"\n".join(ind)+"\n")
    out+=opts+"theorem ju_"+cn+s2+newpost+" := by\n"+pl+bd.rstrip()+"\n\n"
out+="end Fv256.Amd64.UnmarshalJSON\n"
open('lean/Fv256/Proofs/Amd64/UnmarshalJSON.lean','w').write(out)
