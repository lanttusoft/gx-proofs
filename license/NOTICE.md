<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# gX proofs — third-party notices

The gX proof sources are licensed under **GPL-3.0-or-later**; see
[`../LICENSE`](../LICENSE). The proof specifications are project-owned work,
with some modules salvaged from the author's earlier Lean work and re-grounded
against gX source; see [`../PROVENANCE.md`](../PROVENANCE.md).

## Build dependencies (not vendored)

The proof build is pinned by `lake-manifest.json` and `lean-toolchain`. No
third-party Lean source is committed to this repository; Lake fetches the
pinned packages.

- **Lean 4 / Mathlib4** — Apache-2.0. Mathlib is pinned at `v4.27.0`
  (`a3a10db0e9d66acbebf76c5e6a135066525ac900` in the manifest).
  - https://github.com/leanprover/lean4
  - https://github.com/leanprover-community/mathlib4
- **plausible** — Apache-2.0.
- **LeanSearchClient** — Apache-2.0.
- **import-graph** — Apache-2.0.
- **ProofWidgets4** — Apache-2.0.
- **aesop** — Apache-2.0.
- **Qq** — Apache-2.0.
- **batteries** — Apache-2.0.
- **Cli** — MIT.

Full Apache-2.0 and MIT-Cli texts are included in this directory:
[`Apache-2.0.txt`](Apache-2.0.txt), [`MIT-Cli.txt`](MIT-Cli.txt).

The exact revisions of every package are recorded in
[`../lake-manifest.json`](../lake-manifest.json). The `.lake/` build cache is
not part of this repository.
