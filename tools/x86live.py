#!/usr/bin/env python3
"""x86live.py DIS [lo hi]: liveness over the straight-line Reciprocal body (objdump -M intel lines "addr: bytes  insn").
Provides parse(dis) -> list of (addr, text, mnem, reads, writes, freads, fwrites) with regs as 64-bit names and slots as ('m',disp)
and live_at(insns, addr_of_cut, end_addr) -> (live regs, live slots, flags_live)."""
import re, sys
R64 = ['rax','rcx','rdx','rbx','rsp','rbp','rsi','rdi'] + ['r%d'%i for i in range(8,16)]
ALIAS = {}
for i,r in enumerate(R64):
    ALIAS[r]=r
for a,b in [('eax','rax'),('ecx','rcx'),('edx','rdx'),('ebx','rbx'),('esi','rsi'),('edi','rdi'),('ebp','rbp'),('esp','rsp'),
            ('al','rax'),('cl','rcx'),('dl','rdx'),('bl','rbx'),('ax','rax'),('cx','rcx'),('dx','rdx'),('bx','rbx')]:
    ALIAS[a]=b
for i in range(8,16):
    for suf in ['d','w','b']:
        ALIAS['r%d%s'%(i,suf)]='r%d'%i
def regs_in(txt):
    return [ALIAS[t] for t in re.findall(r'[a-z0-9]+',txt) if t in ALIAS]
FREAD = {'adc','sbb','cmovne','cmove','cmovl','cmovg','je','jne','jbe','jb','ja','jae','jl','jg','sete','setne','cmovb','cmovae','cmova','cmovbe','cmovle','cmovge'}
FWRITE_FULL = {'add','sub','and','or','xor','cmp','test','neg','shl','shr','sar','adc','sbb','mul','imul','bsr','div'}
def parse(dis):
    out=[]
    for line in open(dis):
        m=re.match(r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(.*)$',line.rstrip())
        if not m: continue
        addr=int(m.group(1),16); text=m.group(3).strip()
        if not text: continue
        mn,_,ops=text.partition(' '); ops=ops.strip()
        rd=set(); wr=set(); mrd=set(); mwr=set()
        parts=[p.strip() for p in re.split(r',(?![^\[]*\])',ops)] if ops else []
        def memslot(p):
            mm=re.search(r'\[rsp(?:\+(0x[0-9a-f]+))?\]',p)
            if mm: return ('m', int(mm.group(1),16) if mm.group(1) else 0)
            return None
        def isreg(p): return p in ALIAS
        def use(p):  # read of operand p
            if '[' in p:
                for r in regs_in(p.split('[')[1]): rd.add(r)
                ms=memslot(p)
                if ms: mrd.add(ms)
                elif 'rsp' not in p and 'rip' not in p: mrd.add(('x',p))
            elif isreg(p): rd.add(ALIAS[p])
        def setd(p):
            if '[' in p:
                for r in regs_in(p.split('[')[1]): rd.add(r)
                ms=memslot(p)
                if ms: mwr.add(ms)
            elif isreg(p): wr.add(ALIAS[p])
        fr = mn in FREAD; fw = mn in FWRITE_FULL
        if mn in ('mov','movabs'):
            setd(parts[0]); use(parts[1])
        elif mn=='lea':
            wr.add(ALIAS[parts[0]]); 
            for r in regs_in(parts[1]): rd.add(r)
        elif mn in ('movups',):
            if '[' in parts[0]: setd(parts[0])
            else: pass
        elif mn=='xor' and parts[0]==parts[1] or mn=='xor' and ALIAS.get(parts[0])==ALIAS.get(parts[1]) and parts[0] in ALIAS:
            setd(parts[0])
        elif mn in ('add','sub','and','or','xor','adc','sbb','shl','shr','sar'):
            use(parts[0]); setd(parts[0]); use(parts[1])
            if parts[1]=='cl': rd.add('rcx')
        elif mn in ('cmp','test'):
            use(parts[0]); use(parts[1])
        elif mn in ('neg','not','inc','dec'):
            use(parts[0]); setd(parts[0])
        elif mn.startswith('cmov'):
            use(parts[0]); setd(parts[0]); use(parts[1])
        elif mn=='bsr':
            use(parts[1]); use(parts[0]); setd(parts[0])
        elif mn=='mul':
            use(parts[0]); rd.add('rax'); wr.update(['rax','rdx'])
        elif mn=='imul':
            use(parts[0]); use(parts[1]); setd(parts[0])
        elif mn=='div':
            use(parts[0]); rd.update(['rax','rdx']); wr.update(['rax','rdx'])
        elif mn in ('nop','xchg','data16','push','pop','ret','call','jmp') or mn.startswith('j'):
            pass
        else:
            raise Exception('unknown '+text)
        out.append(dict(addr=addr,text=text,mn=mn,rd=rd,wr=wr,mrd=mrd,mwr=mwr,fr=fr,fw=fw))
    return out
def live_at(ins,cut,end):
    """live regs/slots at address `cut` considering instructions in [cut,end) and everything after `end` live-all unless end==None"""
    seq=[i for i in ins if cut<=i['addr']<(end if end else 10**9)]
    live_r=set(); live_m=set(); dead_r=set(); dead_m=set(); flag_live=False; flag_done=False
    for i in seq:
        for r in i['rd']:
            if r not in dead_r: live_r.add(r)
        for m in i['mrd']:
            if m not in dead_m: live_m.add(m)
        if i['fr'] and not flag_done: flag_live=True; flag_done=True
        if i['fw'] and not i['fr'] and i['mn'] not in ('mul',) : flag_done=True
        for r in i['wr']:
            if r not in live_r: dead_r.add(r)
        for m in i['mwr']:
            if m not in live_m: dead_m.add(m)
    return live_r,live_m,flag_live
if __name__=='__main__':
    ins=parse(sys.argv[1]); cut=int(sys.argv[2],16); end=int(sys.argv[3],16) if len(sys.argv)>3 else None
    r,m,f=live_at(ins,cut,end); print(sorted(r),sorted(m),f)
