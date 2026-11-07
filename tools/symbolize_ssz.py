#!/usr/bin/env python3
"""Replace link-time address literals in an SSZ *Main proof by their symbolic names (layout independence).
usage: symbolize_ssz.py FILE ARCH(arm64|amd64)"""
import re,sys
p,arch=sys.argv[1],sys.argv[2]
s=open(p).read()
if arch=='arm64':
    lits={'977152':'fmtAddr','857504':'tErr','834592':'tInt','1004776':'c32Addr'}
    s=re.sub(r'\b977152#64','(BitVec.ofNat 64 fmtAddr)',s)
else:
    lits={'5151169':'fmtAddr','5031392':'tErr','5008480':'tInt','5178744':'c32Addr','4926534':'errRet','4927078':'errRet'}
    s=re.sub(r'\b5151169#64','(BitVec.ofNat 64 fmtAddr)',s)
for k,v in lits.items(): s=re.sub(r'\b'+k+r'\b',v,s)
fn=re.search(r'segWord Extracted.program "([^"]+)"',s)
if arch=='arm64':
    name=fn.group(1)
    add=f'''/-- The address of the constant `32` (the third `fmt.errorf` argument), recomputed from the `ADRP`+`ADD` words. -/
def c32Addr : Nat :=
  adrpLdTarget (Extracted.entry + 0x60) (segWord Extracted.program "{name}" 24)
    (segWord Extracted.program "{name}" 25) 0

'''
    s=s.replace('/-- The text of the error:',add+'/-- The text of the error:',1)
else:
    add='''/-- The address of the constant `32` (the third `fmt.errorf` argument), recomputed from the `LEA` at `entry + 0x7c`. -/
def c32Addr : Nat := ripTarget Extracted.program (Extracted.entry + 0x7c)

/-- The return address of the `fmt.errorf` call (the instruction after it). -/
def errRet : Nat := Extracted.entry + 0xa6

'''
    s=s.replace('/-- The text of the error:',add+'/-- The text of the error:',1)
open(p,'w').write(s)
