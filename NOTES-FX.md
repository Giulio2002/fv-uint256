# NOTES-FX (HANDOVER)
Branch fv/fx (from fv/master 7eda39d): bc420886, 532c5f8d, 7d208dce. Pin lean/lakefile.toml -> janus edcc7b3b (DO NOT merge the pin).
Fixes: MustFromBig amd64 dataLoaded `decide +kernel`; MarshalJSON both ISAs + SetFromHex amd64 find data objects by symbol/address (no data[N]);
Format both ISAs: dec_call hypotheses named by content (lean/Fv256/GrabEq.lean: grab_eq, grab_frame_last, clear_frame_imps).
Root cause Format: dec_summary_ext's new `v<100 -> MemFrame` conjunct shifted rename_i, and left in context made simp's omega disch time out.
Logs: fxwork/log-*, fxwork/fresh-arm64-Format (32G, 3.76 GB RSS), fxwork/sorry/log-* (sorry audits), fxwork/diag-amd64-Format (diagnostic binary).
