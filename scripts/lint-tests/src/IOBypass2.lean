import Lean
open IO Lean Elab Command
run_cmd do
  FS.writeBinFile "/tmp/x" (ByteArray.mk #[1])
@[init] def initX : IO Unit := pure ()
