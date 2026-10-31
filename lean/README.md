# Fv256: proofs about compiled Go

A Lake package of Lean proofs about Go machine code, checked by
[janus](https://github.com/Giulio2002/Janus). It depends on the `janus` Lean library
(see `lakefile.toml`); `janus verify` checks that the dependency is exactly the framework
the verifier carries.

## First verification

```sh
mkdir -p artifacts
(cd go && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o ../artifacts/hello-arm64 .)
janus list artifacts/hello-arm64 --filter main.
janus extract artifacts/hello-arm64 main.Add artifacts/Add
janus verify artifacts/Add --proof Fv256/Add.lean --proof-root . --theorem Fv256.Add.correctness
janus explain artifacts/Add/verified.json
```

## Layout

* `Fv256/Spec.lean`: specifications and lemmas. It does not import `Extracted`; `lake build`
  builds it, and janus reuses its build for every extraction.
* `Fv256/Add.lean`: the theorem about `main.Add`. It imports `Extracted`, the module
  `janus verify` generates from `artifacts/Add`; build it with `janus verify`, not `lake build`.
* Add a module per function. To check several at once, list them in a requests file for
  `janus verify-batch` (see docs/CONSUMERS.md in the Janus repository).

Do not add an `Extracted.lean` here: that module name is reserved for the extraction.
After changing the janus revision in `lakefile.toml`, run `lake update janus`.
