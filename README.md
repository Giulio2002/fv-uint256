# fv-uint256

Machine-checked proofs, with [Janus](https://github.com/Giulio2002/Janus) (Lean 4), that the **compiled arm64 and amd64 machine code** of
[holiman/uint256](https://github.com/holiman/uint256) computes what an independent mathematical specification says.

**Result (2026-11-09):** all 293 rows verified (146 functions on arm64 and amd64, plus 1 amd64v3 row) with Janus [`722bf8ae`](https://github.com/Giulio2002/Janus/commit/722bf8ae933098c6244f3f3e514c17b840bfde38), every main theorem paired with a kernel-checked returning-run witness (no run-free or refutation rows). Fresh-cache full run: 3.9 h wall (6 rows in parallel), 17.8 h summed; slowest row amd64 Scan 3443 s. Release lint (`make lint`) clean. Janus binary built reproducibly (`go build -trimpath -buildvcs=false`, Go 1.26.10), sha256 `44d314819d6f9925c90e9f6e4db8866f92dbc152010691e93877f9ad6aadad54`.

## What is verified

* Library: `github.com/holiman/uint256` master `48f3f44` (`v1.3.3-0.20261018174624-48f3f4483d41`), built by the harness in `go/`.
* Scope: **146 exported functions and methods**, each on **linux/arm64 and linux/amd64**, plus **one extra amd64 row** for the
  `GOAMD64=v3` build of `BitLen`. The table with the per-row status and runtime contracts is [`docs/COVERAGE.md`](docs/COVERAGE.md).
* For every row, `correctness` says: for every admissible call (any caller, any other register or memory content, aliasing as stated in
  the precondition) the code returns without faulting or panicking, obeys the Go ABI, and leaves results and memory exactly as the
  specification (`lean/Fv256/Spec/`, plain mathematics on `Nat`) says. Each main theorem is paired with a kernel-checked `Witness.nonvacuous`: a returning run from a state satisfying the precondition (and a call-site state for every runtime contract), so the statement is not empty; Janus refuses a theorem without it.
* The instruction bytes are copied by `janus extract` out of the linked executable; Lean decodes and runs them in its ISA model.
  Janus's kernel replay and audit check every theorem.

What a reader must trust, and the known limitations, are listed in [`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md).

## Toolchain

| component | version |
|---|---|
| Lean | `leanprover/lean4:v4.34.1` (`lean/lean-toolchain`) |
| Janus | pinned in `lean/lakefile.toml` (`rev`, with `lean/lake-manifest.json`) |
| Go | `go1.26.0` (`GOTOOLCHAIN=go1.26.0`, `CGO_ENABLED=0`, `-trimpath`); the harness hashes are pinned in `scripts/harness.sha256` |
| Other | `python3`, GNU `time`, `memcap` (per-row memory cap used by `verify-all.sh`), `lake` |

You need a built `janus` binary (`go build ./cmd/janus` in the Janus repository) and pass it as `JANUS=/path/to/janus`.

## Running the checks

A `Makefile` wraps the entry points (`make help` lists them):

| command | what it does |
|---|---|
| `make build` | `lake build` of the `Fv256` library (the extraction-independent modules: specification and lemmas) |
| `make verify` | `scripts/verify-all.sh`: build the harness, extract and `janus verify` every row (arm64, amd64, amd64v3) |
| `make verify FN=Add` / `make verify ISA=arm64` | one function / one ISA |
| `make audit` | audit only (`JANUS_STOP_AFTER_AUDIT=1`: the statement audit without the kernel replay of the proofs) |
| `make lint` | `RELEASE=1 scripts/no-sorry.sh`: no `sorry`/axioms/`native_decide`, source and Lean-level lints, spec-closure check, generated-module check |
| `make check-generated` | generated proof modules equal their generators' output |
| `make clean` | remove `build/` |

Environment: `JANUS` (path of the janus binary), `JANUS_CACHE_DIR` (must be a fresh empty directory for a release run), `ROWS`
(rows verified in parallel, default 1), `MEMCAP` (per-row memory cap, default 24G), `PER_FN_TIMEOUT`. See the header of `scripts/verify-all.sh`.
A full run takes many hours; a single row takes minutes to about an hour.

Example: `make verify JANUS=$HOME/janus/bin/janus FN=Add ISA=arm64`.

## Layout

```
README.md          this file
Makefile           entry points
docs/              COVERAGE.md (status table), HUMAN-REVIEW.md (what to review), DEVELOPMENT.md (tooling and proof techniques)
go/                the harness: a program linking every exported uint256 function (its binary is pinned by hash)
lean/              Lake package `fv256`
  Fv256/Spec/        the specification and every definition a theorem STATEMENT depends on (reviewed by a human)
  Fv256/Proofs/      proofs and proof-only definitions: Arm64/, Amd64/, Amd64v3/, Common/
scripts/           verify-all.sh, lints (no-sorry.sh, lint_source.py, check-spec-closure, check-lean-lint), generators, pinned data files
WIP-SORRY.txt      allowlist of unfinished modules for `no-sorry.sh`; empty at release
```

`Spec/` never imports `Proofs/`; `scripts/check-spec-closure` proves, with Lean itself, that every final theorem statement depends only on
`Spec/`, Janus and the extraction.
