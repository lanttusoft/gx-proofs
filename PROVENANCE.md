<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Provenance

- **Snapshot:** the v0.18.0 proof snapshot was exported on 2026-10-30 from the
  author's private gX tree at `64f1c3c` plus the current proof working tree.
  The corresponding public engine release is gX v0.18.0 at
  `0195a3e3e476d5f69dbcd52ea3a9d3d9ada8a9c9`.
- **Ownership:** the proof specifications and proofs are project-owned work.
  The author reviewed and owns the published snapshot.
- **Salvage:** some modules were salvaged from the author's earlier gameX
  `lean/` experiments. They were re-grounded and re-verified against the
  current gX source; stale gameX-specific values and scenes were rejected.
  No gameX assets, story content, or private runtime data are included.
- **AI assistance:** AI-assisted changes are marked in the source and disclosed
  in [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md). AI output is reviewed, but review
  is not a guarantee; see the disclaimer.
- **Dependencies:** Lean 4, Mathlib4, and the Lake dependency set are external
  Apache-2.0/MIT packages, not vendored. `lake-manifest.json` pins exact
  revisions; see [`license/NOTICE.md`](license/NOTICE.md).
- **Kernel trust:** the v0.18.0 snapshot passes the proof audit with 117
  reachable modules and 2,869 theorem declarations using only the standard
  axioms `propext`, `Classical.choice`, and `Quot.sound`. No project axioms or
  `sorry` placeholders are present. This is a kernel/trust result, not a
  translation or GPU-execution certificate.
