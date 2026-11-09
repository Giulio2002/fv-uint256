# fv-uint256: entry points for building and checking the proofs. `make help` lists them.
#
# Environment variables (all optional unless noted):
#   JANUS             path of the janus binary (required by verify, audit and lint; default: `janus` on PATH)
#   JANUS_CACHE_DIR   Janus result cache; a release run needs a FRESH EMPTY directory (default: a new build/jcache-<stamp>)
#   ROWS              rows verified in parallel (default 1)
#   MEMCAP            per-row memory cap (default 24G); LEAN_NUM_THREADS, PER_FN_TIMEOUT: see scripts/verify-all.sh
#   FN                verify only these functions, e.g. FN=Add or FN="Add Sub"
#   ISA               verify only this ISA: arm64, amd64 or amd64v3
SHELL := /usr/bin/env bash
JANUS ?= janus
export JANUS
export JANUS_CACHE_DIR
export ROWS
export MEMCAP

.PHONY: help build verify audit lint check-generated clean

help:
	@sed -n '2,10p' Makefile
	@echo
	@echo "targets: build verify audit lint check-generated clean"

# lake build of the Fv256 library (specification and lemmas; needs lake and the pinned Janus package).
# Env: none beyond the toolchain in lean/lean-toolchain.
build:
	cd lean && lake build Fv256

# Extract and `janus verify` every row of docs/COVERAGE.md. Env: JANUS, JANUS_CACHE_DIR, ROWS, MEMCAP; FN=... and ISA=... select a subset.
verify:
	ONLY_ISA="$(ISA)" scripts/verify-all.sh $(FN)

# Audit only: the statement audit and non-vacuity check, without the kernel replay of the proofs. Env: as `verify`.
audit:
	JANUS_STOP_AFTER_AUDIT=1 ONLY_ISA="$(ISA)" scripts/verify-all.sh $(FN)

# Release lint: no sorry/axioms, source and Lean-level lints, spec closure, generated modules. Env: JANUS (needed for the spec survey).
lint:
	RELEASE=1 scripts/no-sorry.sh

# Generated proof modules must equal the output of their generators (never writes tracked files). Env: none.
check-generated:
	bash scripts/check-generated.sh

# Remove build outputs (harness binaries, extractions, caches, logs, survey workspaces). Env: none.
clean:
	rm -rf build
