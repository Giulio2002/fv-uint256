import Extracted
import Fv256.ChainProg
import Fv256.CodeIn

open Janus.Amd64.Tactic

set_option maxRecDepth 100000 in
theorem hc : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem linked (impl : List Janus.Amd64.Segment) {entry : Nat} {pre : Janus.Amd64.State → Prop}
    {post : Janus.Amd64.State → Janus.Amd64.State → Prop} (h : Summary Fv256.ChainProg.program entry pre post) :
    Summary (Extracted.program.link impl) entry pre post := Fv256.CodeIn.lib_summary_link impl hc h
