#!/usr/bin/env python3
"""mkfinal_amd64.py R4IMPORT R4NAME : write the four amd64 final files (MulMod, MulModWithReciprocal, IMulMod, IMulModWithReciprocal)
from the *Corr / *Core param files by dropping the reduce4 hypothesis and instantiating it with R4NAME."""
import re, sys
imp, r4 = sys.argv[1], sys.argv[2]
D = "lean/Fv256/Amd64/"
def stmt(path, name):
    t = open(D + path).read()
    a = t.index("theorem correctness_param")
    b = t.index(":=", t.index("Ensures", a))
    # the statement ends at the first ':=' after the post-condition; find ':= by' or ':=\n'
    m = re.search(r":=\s*(by\b|\n)", t[a:])
    b = a + m.start()
    s = t[a:b]
    s = s.replace("theorem correctness_param (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) ", "theorem correctness ")
    return s
for fn, core, args, ns, coremod in [
    ("MulMod", "MulModCorr.lean", "z x y m", "MulMod", "Fv256.Amd64.MulModCorr"),
    ("MulModWithReciprocal", "MulModRecCorr.lean", "z x y m mu", "MulModWithReciprocal", "Fv256.Amd64.MulModRecCorr"),
    ("IMulMod", "IMulModCore.lean", "z x m", "IMulMod", "Fv256.Amd64.IMulModCore"),
    ("IMulModWithReciprocal", "IMulModWithReciprocalCore.lean", "z x m mu", "IMulModWithReciprocal", "Fv256.Amd64.IMulModWithReciprocalCore")]:
    s = stmt(core, "")
    wit = {"MulMod": "MulModWit.lean", "MulModWithReciprocal": "MulModRecWit.lean"}.get(fn)
    modname = coremod.split(".")[-1]
    hdr = f"import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.SpecF\nimport Fv256.Amd64.{modname}\nimport {imp}\n\nopen Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\n\nnamespace Fv256.Amd64.{ns}\n\n"
    body = s + f" :=\n  {coremod}.correctness_param {r4} {args}\n\n"
    if wit:
        w = open(D + wit).read()
        i = w.index("namespace ")
        wbody = w[i:]
        wbody = re.sub(r"namespace Fv256\.Amd64\.\w+\.Witness", "namespace Witness", wbody, 1)
        wbody = re.sub(r"end Fv256\.Amd64\.\w+\.Witness", "end Witness", wbody)
        # the head of the witness file has set_option lines before namespace; keep them
        pre = w[w.index("open Janus.Contracts") if False else 0:i]
        extra = "".join(l + "\n" for l in pre.split("\n") if l.startswith("set_option"))
        out = hdr + body + extra + wbody + f"\nend Fv256.Amd64.{ns}\n"
    else:
        out = hdr + body + f"-- witness: see below\n\nend Fv256.Amd64.{ns}\n"
    open(D + fn + ".lean", "w").write(out)
    print("wrote", fn)
