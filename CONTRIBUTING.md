<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Contributing

Proof changes must:

- build the core tier with `make build-core`;
- build both Mathlib tiers with `make build-full` when the change touches them;
- pass `make audit` (and `make audit-full` for Mathlib changes);
- keep the family roots importing every module;
- avoid `sorry`, `admit`, project axioms, and nonstandard dependencies;
- add a short source-correspondence note when a specification is re-grounded
  against the C implementation;
- keep the GPL-3.0-or-later SPDX header and AI marker conventions;
- disclose AI assistance in the commit/PR description where applicable.

See [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md), [`PROVENANCE.md`](PROVENANCE.md),
and the engine's
[contribution guide](https://github.com/lanttusoft/gX/blob/main/CONTRIBUTING.md).
