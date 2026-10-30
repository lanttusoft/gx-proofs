# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (c) 2025-2026 lanttu, opencode
# This file is part of gX proofs. See LICENSE.

.PHONY: deps build build-core build-full audit audit-full clean

deps:
	lake update

build: build-core

build-core:
	lake build GxProofs

build-full:
	lake build GxProofsGfx GxMath

audit:
	python3 scripts/proof_audit.py

audit-full:
	python3 scripts/proof_audit.py --full --no-build

clean:
	rm -rf .lake/build
