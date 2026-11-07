# Draft: decimal wrappers (text only; compile when FV-I3 commits an Extracted-free SfdTopSpec)
Source: uint256 master 48f3f44 decimal.go / conversion.go. Spec base: Fv256.I.decParse b n : Res = ok v | eof | range | syntax lo len (SpecI.lean on fv/wi).

## FromDecimal(s) (*Int, error)   [Go: var z Int; if err := z.SetFromDecimal(s); err != nil {return nil, err}; return &z, nil]
 string (ptr RAX, len RBX) -> (*Int RAX, error itab RBX, data RCX).  z is a heap temp (newobject) or stack escape.
 decParse = ok v  -> RAX = non-nil ptr p, 32 bytes at p = v, error = nil (RBX=RCX=0)
 eof / range / syntax -> RAX = 0, error as SetFromDecimal's (io.EOF | ErrBig256Range | *strconv.NumError{Func "ParseUint", Num chunk, Err ErrSyntax})
 NOTE: for range the callee leaves z unchanged but FromDecimal returns nil, so z content is irrelevant.
## MustFromDecimal(s) *Int  : ok v -> ptr with v; otherwise gopanic(err) (call into runtime.gopanic; statement: execution never returns normally -> needs the panic stub/`Panics` form of Ensures used by the other Must* proofs, cf. MustFromBig/MustFromHex).
## UnmarshalText(input []byte) error  [z=RAX, ptr RBX, len RCX, cap RDI]
 if len>=2 && input[0]=='0' && input[1] in {'x','X'}: z.fromHex(string(input)) (hex path: reuse the SetFromHex-family summary; spec = FV SetFromHex of the same string)
 else z.SetFromDecimal(string(input)): result per decParse as above. string(input) conversion copies (slicebytetostring runtime contract; SBTS contract exists in pin).
## UnmarshalJSON(input []byte) error
 if len<2 || input[0] != '"' || input[len-1] != '"': z.SetFromDecimal(string(input))  (unquoted: decimal only)
 else UnmarshalText(input[1:len-1])  (quoted: hex if 0x/0X prefix else decimal)
 Edge: input = `"` (len 1) -> unquoted path -> syntax error on `"`; input = `""` -> UnmarshalText("") -> SetFromDecimal("") -> io.EOF.
## Scan(src any) error
 nil -> Clear, nil; string s / []byte b -> scanScientificFromString; other type -> errors.New("unsupported type") (new error object, message "unsupported type").
 scanScientificFromString(src): len 0 -> Clear, nil; no 'e': SetFromDecimal; with 'e' at idx (FIRST 'e'): z := SetFromDecimal(src[:idx]) (error returned as is); exponent text src[idx+1:]=="0" -> nil; else exp := SetFromDecimal(exponent text) (error as is); exp > 77 -> ErrBig256Range; exp = 10^exp; z, ov := z*exp; ov -> ErrBig256Range (z holds the wrapped product).
 => needs Exp, MulOverflow, GtUint64 summaries (all verified on at least arm64/amd64 per COVERAGE) + strings.IndexByte (assembly/IndexByteString: needs a library contract or proof) + type switch on iface (type descriptor pointers in rodata: TD of string / []byte).
 Order of work: FromDecimal -> UnmarshalText (needs hex) -> UnmarshalJSON -> MustFromDecimal -> Scan (heaviest).
## Hypotheses to take: hsfd : Summary (Extracted.program.link impl) sfdEntry SfdTopPre SfdTopPost and hif hnew hmg hmv hwb1 hwb2 as in SfdPw.pw_sum.

## Findings 2026-11-06 late (amd64 code shape, SfdTopSpec 0e29fd7)
- SfdTopSpec: structure SfdCfg (all binary addresses as fields), TopPre/TopPost/SfdSummary C P entry R R2 T b L lo hi z pS nS; window lo+4800 <= RSP.
- UnmarshalText (72 instrs): len>=2 && b[0]=='0' && b[1] in {x,X} -> runtime.slicebytetostring (SBTS runtime contract, allocates via mallocgc => heap model R/R2/b/L like SetFromDecimal's) then (*Int).fromHex; else slicebytetostring then SetFromDecimal. Needs: SBTS contract (pin 655a23fa has slicebytetostringSpec with staticuint64s addr), fromHex library summary (FV-C hex family / SetFromHex), SfdSummary.
- UnmarshalJSON (52): unquoted -> same as text's decimal branch; quoted -> tail call/jump UnmarshalText on input[1:len-1].
- FromDecimal (44) / MustFromDecimal (45): newobject(Int) + SetFromDecimal (+ gopanic for Must).
- Scan (95): type switch + scanScientificFromString (IndexByte, Exp, MulOverflow, GtUint64).
- All of them share the heap/runtime-model plumbing of SetFromDecimal (R, R2, T, b, L, hif hnew hmg hmv hwb1 hwb2): the wrappers' Pre should be TopPre-like for the callee plus the wrapper's own stack window; start with UnmarshalJSON/UnmarshalText once FV-I3's top proof (extCfg) closes, since every wrapper needs `extCfg` to instantiate SfdSummary on Extracted.

## Spec-level statements for UnmarshalText / UnmarshalJSON (2026-11-07, to write once the SfdTopSpec Mod fix lands)
Notation: bs = bytes of the input slice (ptr p, len n, cap c); dec(bs) := Fv256.I.decParse (bytesAt mem p) n; hex(bs) := parseHex (FV-C's HexLemmas / SetFromHex spec).
- UnmarshalText(z, input): let isHex := n >= 2 ∧ b0 = '0' ∧ (b1 = 'x' ∨ b1 = 'X').
    isHex  -> result of z.fromHex(string(input)) : ok v -> z = v, err nil; error e -> the fromHex error (ErrEmptyNumber/ErrSyntax/ErrBig256Range/leading-zero variants per hex spec), z unspecified/zeroed per hex spec.
    ¬isHex -> result of SetFromDecimal(string(input)): the four decParse outcomes exactly as for FromDecimal (z updated only on ok / eof zeroes z / range leaves z / syntax unspecified).
  Both branches copy the input first (runtime.slicebytetostring; for n <= 32 it uses the caller's 32-byte stack buffer, no allocation): the object copied is outside the live set and does not change the bytes the parser sees (str_read-style lemma needed for the copy).
- UnmarshalJSON(z, input): quoted := n >= 2 ∧ b0 = '"' ∧ b[n-1] = '"'.
    ¬quoted -> as the decimal branch above on the whole input (so `"` alone and ` 12` are syntax errors; unquoted hex is a syntax error).
    quoted  -> UnmarshalText on input[1:n-1] (so `"0x1f"` hex, `"12"` decimal, `""` -> io.EOF, `"0x"` -> hex error).
- Both need: the slicebytetostring runtime contract (hypothesis, from the pin's U-SBTS-POST), a Live heap (R, b, L) budget for the copy, and the SfdSummary hypothesis for the decimal branch; UnmarshalText additionally the amd64/arm64 fromHex library summary (FV-C family; check it is over a library program, not Extracted).
