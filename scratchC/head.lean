import Extracted
import Fv256.Amd64.MsaDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)

namespace Fv256.Amd64.Msa

open Fv256.Msa

/-- the element type of the byte slice, an argument of every `growslice` call -/
abbrev ga : Nat := Extracted.program.contractAddr "runtime.growslice"

abbrev u8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

