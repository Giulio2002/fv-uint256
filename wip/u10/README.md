# U10 repros (frozen, read-only copies; FV-B)

1. arm64 Div64 summary: janus_run blows up with a large conjunction in the context.
   `arm64-div64/` = copy of /srv/janus-ops/repros/U10-fvb-div64/ (README.md, Repro.lean, ex-arm64-Div extraction, run.sh, time1.log).
2. amd64 `partB` of `(*Int).DivMod` (file `DivModB-current.lean`, lean/Fv256/Amd64/DivModB.lean on fv/wb):
   `janus64_run [...] calls [summary_link impl UdivremM.udivrem_rem_s]` with ~25 hypotheses (several disjunctive address facts
   hdz hdx hdy hdm hzm hdg, limb bounds hx0..hy3) costs 875 s (branch-pruning omega calls 0.5-10 s each, ~67 of them) plus 292 s in the
   following all_goals; total 1488 s with profiler on.
   - `dmb7-profile.log.gz` = full profiler/trace.profiler log (150 MB uncompressed) of that run, `dmb7-summary.txt` = top-level step times.
   - extraction: /srv/fv-uint256-wB/build/ex-amd64-DivMod (Extracted.lean + identity.json); modules compile with
     `cd /srv/fv-uint256-wB && tools-local/lean1d.sh amd64 DivMod DivModB 3000` (needs build/olean-d, framework path in lean1d.sh).
Janus pin used: deeprec framework f65043ca (/srv/fv-uint256-wB-deeprec/fw-keep/de1f0997b092221ed98af24d).
