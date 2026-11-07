import re,sys
p=sys.argv[1]
s=open(p).read()
s=s.replace('  janus64_data hd [hw4]\n','  janus64_data hd [hw4]\n  janus_eval_nat hFA : fmtAddr\n  janus_eval_nat hC32 : c32Addr\n  janus_eval_nat hER : errRet\n  janus_eval_nat hTI : tInt\n  janus_eval_nat hTE : tErr\n',1)
s=s.replace('  janus_eval_nat hFA : fmtAddr\n  rw [hFA] at hok\n','',1)
s=s.replace('  rw [hFA] at hok\n','',1)
s=re.sub(r'rw \[Arm64\.Memory\.readLE_writeLE_self\]\)','rw [Arm64.Memory.readLE_writeLE_self]; try omega)',s)
s=re.sub(r'(have hm0 :[^\n]*\n[^\n]*\n[^\n]*rw \[Arm64\.Memory\.readLE_writeLE_self\])\n',r'\1; try omega\n',s,count=1)
a='(by simp [setRegF]) (by simp [setRegF])\n      (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])\n      (by simp [setRegF, hsp104, Arm64.Memory.readLE_writeLE_self])'
assert a in s
s=s.replace(a,'(by simp [setRegF, hFA]) (by simp [setRegF])\n      (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])\n      (by simp [setRegF, hsp104, Arm64.Memory.readLE_writeLE_self, hER])',1)
open(p,'w').write(s)
