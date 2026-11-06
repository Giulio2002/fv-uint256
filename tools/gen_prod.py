import sys
sys.path.insert(0,'/srv/fv-uint256-wf/tools')
import g4arith
adc,_,_,W=g4arith.unit_chain([0x3ea,0x429,0x46b,0x47f],'adcB',['x47frbx','x47frsi','x47fr8','x47frax','x47fr11'])
q=['x2f8rax','x2f8rdx','x2f8rcx','x2f8r10','x2f8r8']; m=['x2f8m60','x2f8m68','x2f8m70','x2f8rdi']
t,units,inact,om=g4arith.prod_units([0x2f8,0x33e,0x38b,0x3ea],'prodS2',W[0],q,m)
hdr="import Fv256.Amd64.R4Seg0\n\nset_option exponentiation.threshold 400\nnamespace Fv256.Amd64.R4Seg\n\ntheorem mulb (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b < 2 ^ 128 := by\n  have := Nat.mul_lt_mul'' ha hb\n  rwa [← Nat.pow_add] at this\n\n"
open('/srv/fv-uint256-wf-r4/lean/Fv256/Amd64/R4ArithP.lean','w').write(hdr+t+"\nend Fv256.Amd64.R4Seg\n")
