<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# gX proofs

Lean 4 specifications and proofs for gX engine behavior that unit tests cannot
pin: coordinate-mapping round trips, viewport containment, input protocols,
editor state machines, matrix upload conventions, RHI state machines, draw
protocols, easing curves, and the gxmath foundation.

This repository is published separately from the gX engine release. It is not
part of the engine source tarball or executable.

## Tiers

- **`GxProofs`** — core-only, blocking tier. Nat/Bool specifications and core
  tactics; no Mathlib imports. This is the tier the engine's `make proofs`
  gate builds.
- **`GxProofsGfx`** — Mathlib tier for renderer, RHI, temporal, postprocess,
  weather, audio, and cross-check contracts.
- **`GxMath`** — Mathlib tier for the gxmath algebra, geometry, calculus,
  Fourier, color, conversion, easing, and physics contracts.

Some specifications were salvaged from the author's earlier Lean work and
re-grounded against the current gX source. See [`PROVENANCE.md`](PROVENANCE.md).

## Build

Requirements:

- [elan](https://github.com/leanprover/elan) with the pinned toolchain in
  [`lean-toolchain`](lean-toolchain) (Lean 4.27.0)
- Lake (installed with Lean)

```bash
lake update          # fetch the pinned dependency graph once
make build-core      # lake build GxProofs
make build-full      # lake build GxProofsGfx GxMath (Mathlib cache recommended)
```

`lake-manifest.json` pins the exact dependency revisions. `.lake/` is
machine-local and is not committed.

## Audit

```bash
make audit           # build and audit the core tier
make build-full
make audit-full      # audit all tiers using the preceding build
```

[`scripts/proof_audit.py`](scripts/proof_audit.py) checks that every module is
reachable from its family root and that theorem dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`. It rejects project axioms and
nonstandard dependencies.

The audit is a kernel/trust audit, not a translation proof. It does **not**
certify that a Lean model matches the C implementation, IEEE floating-point
behavior, GPU execution, or driver behavior. Source correspondence and native
gates remain separate obligations. See the engine's
[`docs/lean_proofs.md`](https://github.com/lanttusoft/gX/blob/main/docs/lean_proofs.md)
and
[`docs/proof_inventory.md`](https://github.com/lanttusoft/gX/blob/main/docs/proof_inventory.md).

[`IMPORTANCE.json`](IMPORTANCE.json) carries the reviewed significance and
evidence catalog; [`SIGNIFICANCE.md`](SIGNIFICANCE.md) defines the scale.
[`ORGANIZATION.md`](ORGANIZATION.md) describes the tier/domain split.

The v0.18.0 snapshot passes the full audit: 117 reachable modules, 2,869
theorem declarations, standard axioms only.

## License

The gX proof sources are licensed under **GPL-3.0-or-later**; see
[`LICENSE`](LICENSE). Lean 4, Mathlib4, and the Lake dependency set are
Apache-2.0/MIT and are not vendored; see [`license/NOTICE.md`](license/NOTICE.md).

AI assistance and its limitations are disclosed in
[`AI_DISCLOSURE.md`](AI_DISCLOSURE.md). The proofs are provided as-is, without
warranty; nothing here is legal, security, or fitness-for-purpose advice.
