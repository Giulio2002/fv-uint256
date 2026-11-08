import Lean
-- FV-IO1 rows: open IO then qualified names without the linted prefixes
open IO Lean Elab Command
run_cmd do
  let b ← FS.readBinFile "/etc/passwd"
  let r ← Process.output { cmd := "id" }
  let e ← getEnv "HOME"
  let t ← monoMsNow
  logInfo m!"{b.size} {r.stdout} {e} {t}"
