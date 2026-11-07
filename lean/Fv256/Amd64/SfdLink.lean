import Fv256.Amd64.SfdLib

/-!
# Consumers: `SfdProg` is part of an extraction (the `CodeIn`/`LibIn` side conditions)

`hLib_of_decide` packages the seven decidable checks that `LibIn SfdProg.program E` needs (the consumer states it for its own
`Extracted.program` and closes it with `by decide` under `set_option maxRecDepth 100000`); `hca_of_decide` does the same for the
contract-address agreement.  `LibIn.progEq` (LinkEq) is the `CodeIn`-style containment: the library program linked with the consumer's remaining code runs like `E.link impl`.
-/

open Janus Janus.Amd64

namespace Fv256.Amd64.SfdLink

theorem hLib_of_decide {E : Janus.Amd64.Program}
    (h1 : ∀ s ∈ E.segments, ∀ s' ∈ E.segments, s' = s ∨ Fv256.CodeIn.Disj s s')
    (h2 : ∀ s ∈ Fv256.Amd64.SfdProg.program.segments, s ∈ E.segments)
    (h3 : ∀ x ∈ Fv256.Amd64.SfdProg.program.stubs, x ∈ E.stubs)
    (h4 : ∀ x ∈ E.stubs, x ∈ Fv256.Amd64.SfdProg.program.stubs)
    (h5 : ∀ x ∈ Fv256.Amd64.SfdProg.program.stubs, ∀ y ∈ Fv256.Amd64.SfdProg.program.stubs, x.addr = y.addr → x = y)
    (h6 : Fv256.Amd64.SfdProg.program.exitAddr = E.exitAddr)
    (h7 : ∀ d ∈ Fv256.Amd64.SfdProg.program.data, d ∈ E.data) :
    Fv256.LinkEq.LibIn Fv256.Amd64.SfdProg.program E := ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem hca_of_decide {E : Janus.Amd64.Program}
    (h : ∀ n ∈ Fv256.Amd64.SfdLib.contractNames, E.contractAddr n = Fv256.Amd64.SfdProg.program.contractAddr n) :
    Fv256.Amd64.SfdLib.ContractsAgree E := h

end Fv256.Amd64.SfdLink
