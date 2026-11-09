import Extracted
import Fv256.Proofs.Amd64.FormatInhabit
import Fv256.Proofs.Amd64.FormatNil

/-!
# `Format` (Amd64): the `fmt.Fprint(w, "<nil>")` call-site contract is inhabited (U-ICALL-INHABITED)

`FpArg data` of `Fv256.Amd64.FormatNil` fixes the type descriptor, string header and bytes at the extraction's data addresses;
`Fv256.Amd64.FormatInhabit.fp_pre_inhabited_gen` builds the call state for any three addresses below `2^40` (header, bytes
disjoint), and this module instantiates it at `strTyA`, `hdrA`, `litA`.
-/

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.ICall

namespace Fv256.Amd64.FormatInhabit

theorem fp_pre_inhabited : ∃ (stack : Nat) (rt : List (Nat × Nat)) (data : BitVec 64) (s : State),
    ICallPre64 5 stack 80 rt (Fv256.Amd64.FormatNil.FpArg data) s :=
  fp_pre_inhabited_gen Fv256.Amd64.FormatNil.strTyA Fv256.Amd64.FormatNil.hdrA Fv256.Amd64.FormatNil.litA
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Fv256.Amd64.FormatInhabit
