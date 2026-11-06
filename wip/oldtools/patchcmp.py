import sys
D=sys.argv[1]
p=f'/srv/fv-uint256/lean/Fv256/{D}/Cmp.lean'
s=open(p).read()
s=s.replace("(s'.regs 0).toNat % 256 = (Spec.cmp (","(s'.regs 0) = BitVec.ofInt 64 (Spec.cmp (")
s=s.replace(").toNat) := by",")) := by",1)
s=s.replace("ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 0 := by","ABIReturn s0 s' ∧ (s'.regs 0) = 0#64 := by")
s=s.replace("bool","int").replace("`int` result (low byte of `X0`)","`int` result (`X0`)").replace("(`AL`, low byte of `RAX`)","(`RAX`)")
open(p,'w').write(s)
