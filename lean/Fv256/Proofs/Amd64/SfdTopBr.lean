import Fv256.Proofs.Amd64.SfdTopCfg
import Fv256.Proofs.Amd64.SfdFdG

/-!
# Bridge: the `extCfg` instance of the Extracted-free statement is the Extracted-level one
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts

namespace Fv256.Amd64.SfdTopBr

open Fv256.Amd64.SfdTopCfg

theorem env_to {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {s : State}
    (h : SfdTopSpec.Env extCfg R R2 T b L lo hi s) : Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi s := h
theorem env_of {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {s : State}
    (h : Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi s) : SfdTopSpec.Env extCfg R R2 T b L lo hi s := h
theorem mod_to {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)}
    (h : SfdTopSpec.Mod extCfg R R2 T L) : Fv256.Amd64.SfdBridge.Mod R R2 T L := h
theorem mult_to {z lo hi : Nat} {m : Janus.Arm64.Memory} (h : SfdTopSpec.MultOK extCfg z lo hi m) :
    Fv256.Amd64.SfdFd.MultOK z lo hi m := h
theorem chunk_to {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b pS nS lo hi : Nat} {m : Janus.Arm64.Memory}
    (h : SfdTopSpec.ChunkAll extCfg R R2 L b pS nS lo hi m) : Fv256.Amd64.SfdFd.ChunkAll R R2 L b pS nS lo hi m := h
theorem teobj_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64} {s s' : State} {q t : Nat}
    (h : Fv256.Amd64.SfdToError.TeObj R b L fp fl sp sl s s' q t) : SfdTopSpec.TeObj extCfg R b L fp fl sp sl s s' q t := h

end Fv256.Amd64.SfdTopBr
