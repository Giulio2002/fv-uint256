import Lean
open Lean

/-! `lean --run scripts/LintImports.lean FILE...`: prints one line per import of each file, parsed by LEAN'S OWN header parser
(`Lean.Elab.parseImports`), so `import A import B` on one line, `import all`, `import runtime`, `prelude` and imports inside comments are
all handled exactly as the compiler would.  Output: `FILE<TAB>MODULE<TAB>flags` (flags: `all`, `runtime`; `prelude` is a pseudo-module line
`FILE<TAB><prelude><TAB>`). -/
def main (files : List String) : IO UInt32 := do
  let mut bad := false
  for f in files do
    let src ← IO.FS.readFile f
    try
      let (imps, _, _) ← Lean.Elab.parseImports src (some f)
      for i in imps do
        let fl := (if i.importAll then "all " else "") ++ (if i.isExported then "" else "private ") ++ (if i.isMeta then "meta " else "")
        IO.println s!"{f}\t{i.module}\t{fl.trimAscii}"
    catch e =>
      IO.eprintln s!"{f}: header parse error: {e}"
      bad := true
  return if bad then 1 else 0
