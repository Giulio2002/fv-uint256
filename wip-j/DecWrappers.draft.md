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
