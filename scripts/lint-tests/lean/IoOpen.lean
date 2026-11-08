import SvyTools
open IO Lean Elab Command
namespace Fv256.T
def readsFile : IO Unit := do
  let _ ← FS.readBinFile "/etc/passwd"
  pure ()
def viaEIO : EIO IO.Error Unit := pure ()
elab "badcmd" : command => do
  let _ ← liftIO (getEnv "HOME")
@[init] def initX : IO Unit := pure ()
end Fv256.T
#lint_io
