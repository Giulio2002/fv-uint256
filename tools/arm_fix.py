import re,sys
p=sys.argv[1]
s=open(p).read()
s=s.replace('  janus_data hd [hw4]\n','  janus_data hd [hw4]\n  janus_eval_nat hFA : fmtAddr\n  janus_eval_nat hC32 : c32Addr\n  janus_eval_nat hTI : tInt\n  janus_eval_nat hTE : tErr\n',1)
s=s.replace('  janus_eval_nat hFA : fmtAddr\n  rw [hFA] at hok\n','',1) if s.count('janus_eval_nat hFA')>1 else s
s=s.replace('  rw [hFA] at hok\n','',1)
s=re.sub(r'rw \[Memory\.readLE_writeLE_self\]\)','rw [Memory.readLE_writeLE_self]; try omega)',s)
s=re.sub(r'(have hm0 :[^\n]*\n[^\n]*\n[^\n]*rw \[Memory\.readLE_writeLE_self\])\n',r'\1; try omega\n',s,count=1)
i=s.index('(key _ (by janus_frame)')
j=s.index('\n',s.index('\n',i)+1)
s=s[:i]+s[i:j].replace('(by simp [setReg])','(by simp [setReg, hFA])')+s[j:]
open(p,'w').write(s)
