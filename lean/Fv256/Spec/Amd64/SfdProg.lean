import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.Amd64.SfdProg

open Janus

/-- ASCII-named literal copies of the addresses the statement (`SfdTopCfg.extCfg`) mentions (the auditor rejects non-ASCII names) -/
def cfgMallocgc : Nat := 0x4784a0

def cfgMemmove : Nat := 0x47fde0

def cfgNewobject : Nat := 0x41d9c0

def cfgWb1 : Nat := 0x47f680

def cfgWb2 : Nat := 0x47f6a0

def cfgIoEOF : Nat := 0x5b7c50

def cfgErrBig : Nat := 0x5b7ba0

def cfgMulTab : Nat := 0x5b8580

def cfgNumErrType : Nat := 0x4d78a0

def cfgNumErrItab : Nat := 0x4f1a00

def cfgErrItab : Nat := 0x4f19e0

def cfgSynConst : Nat := 0x4f09f0

def cfgErrSyntax : Nat := 0x5b7ef0

def cfgWbFlag : Nat := 0x5def20

def cfgFnStr : Nat := 0x4e6568

def cfgMaxStr : Nat := 0x4ef9b4

end Fv256.Amd64.SfdProg
