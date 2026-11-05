import sys
# stdin: generated binary-op file; add the overflow flag result. argv: Ov-spec-name, reg index of 2nd result (arm64: 1, amd64: 3), isa
ov,reg,isa=sys.argv[1],sys.argv[2],sys.argv[3]
s=sys.stdin.read()
if isa=='arm64':
    s=s.replace("(fun s s' => s'.regs 0 = z ∧\n","(fun s s' => s'.regs 0 = z ∧ (s'.regs %s).toNat %% 256 = (Spec.%s (val256 s.mem x.toNat) (val256 s.mem y.toNat)).toNat ∧\n"%(reg,ov))
else:
    s=s.replace("(fun s s' => s'.regs 0 = z ∧\n","(fun s s' => s'.regs 0 = z ∧ (s'.regs %s).toNat %% 256 = (Spec.%s (valueAt s x 32) (valueAt s y 32)).toNat ∧\n"%(reg,ov))
s=s.replace("returns `z` in `X0`,","returns `z` in `X0`, the overflow flag in `X1` (low byte),").replace("returns `z` in `RAX`,","returns `z` in `RAX`, the overflow flag in `RBX` (low byte),")
s=s.replace('refine ⟨h.1, h.2.1, ?_⟩\n  rw [h.2.2.1]','refine ⟨h.1, h.2.1, ?_⟩\n  rw [h.2.2.2.1]')
print(s,end='')
