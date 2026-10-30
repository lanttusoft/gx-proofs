<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Proof organization

This directory has two orthogonal axes:

- **Tier** = the dependency set enforced by a library root and its gate.
- **Domain** = the subject area inside a tier.

Tier names are not domain labels. In particular, `GxProofs` is the
no-Mathlib core tier, not “engine-core subjects only”, and `GxProofsGfx`
contains Mathlib-side audio and generic math contracts as well as graphics.

## Tiers

| Tier | Dependency policy | Gate |
|---|---|---|
| `GxProofs` | Core Lean only; no Mathlib imports | `make proofs`, blocking in `make check` |
| `GxProofsGfx` | Mathlib; graphics, RHI, temporal, weather, audio and cross-check contracts | `make proofs-full`, opt-in |
| `GxMath` | Mathlib; generic gxmath algebra and physics | `make proofs-full`, opt-in |

Every module must be imported by its family root. The engine-side
[`docs/proof_inventory.md`](https://github.com/lanttusoft/gX/blob/main/docs/proof_inventory.md)
is the authoritative module/declaration map; the engine's
`make proof-inventory-check` rejects a stale catalog.

## Domains

Domains use subdirectories without changing the tier policy. Namespaces stay
stable during this pass; the directory path is the domain, not a second name
hierarchy. The current groups are:

- `GxProofs`: core UI, input, RHI-state, temporal, draw-order, renderer
  constants and routing contracts that need no Mathlib.
- `GxProofsGfx`: `Rhi`, `Renderer`, `Temporal`, `Postprocess`, `Weather`,
  `Ssr`, `Audio`, and matrix cross-checks.
- `GxMath`: vector, matrix, quaternion, SDF, Fourier, color, conversion,
  easing, scalar/calculus and physics. `GxMath/Easing.lean` now owns the
  generic easing contracts; `GxProofsGfx/Audio/` owns the audio domain.

Moving a module between domains does not change its tier. Moving it between
tiers changes its dependency and gate obligations.

## Matrix models

There is more than one matrix representation because the contracts answer
different questions. The registry is:

| Model | Module | Role |
|---|---|---|
| Logical row-major `GxMath.Matrix` | `GxMath/Matrix.lean` | Engine source semantics for the 4×4 algebra and transforms |
| Flat field `MatrixField.Matrix` | `GxProofsGfx/Matrix/MatrixField.lean` | Numeric field order, multiply/transpose identities |
| Abstract tuple `MatrixTuple` | `GxProofsGfx/Matrix/MatrixTuple.lean` | Mathlib `Matrix` upload/transpose interpretation |
| Clip `ClipMatrix.Mat4` | `GxMath/ClipMatrix.lean` | Row-vector clip space, NDC/depth and clipping predicates |
| Temporal `TemporalMatrix` | `GxProofsGfx/Temporal/TemporalMatrix.lean` | Camera snapshot/history reconstruction using `Mat4` |
| Ideal inverse `CofactorInverse` | `GxMath/CofactorInverse.lean` | Cofactor/determinant inverse algebra over `Mat4` |
| Camera inverse bridge | `GxProofsGfx/Temporal/CofactorInverse.lean` | Temporal reconstruction using the generic inverse |
| Small matrices | `GxMath/MatrixSmall.lean` | 2×2/3×3 determinant/trace helpers |

`GxProofsGfx/MatrixBridge.lean` records the conversion between the flat field
model and `GxMath.Matrix`, and between the clip `Mat4` model and the logical
matrix. The bridge is a correspondence layer, not a claim that the physical C
struct or GL upload is byte-identical.

Rules for future work:

- New generic algebra belongs in `GxMath`, not `GxProofsGfx`.
- A new matrix representation needs a row in this registry and a bridge or an
  explicit statement of why no bridge exists.
- Do not reuse a namespace for two unrelated matrix models.
- The physical struct order and GL upload convention remain separate premises;
  see `GxProofsGfx.Temporal.TemporalMatrix` and `docs/lean_proofs.md`.

## Planned cleanup

1. Move generic `GfxEasing` to `GxMath`. **Done:** `GxMath/Easing.lean`.
2. Move audio modules under an `Audio` domain (or a fourth Mathlib tier if the
   group grows). **Done:** `GxProofsGfx/Audio/`.
3. Decide whether `ClipMatrix`/`CofactorInverse` should move to `GxMath`.
   **Done:** the clip model and generic cofactor/inverse algebra moved; the
   camera-history reconstruction remains as `Temporal.CofactorInverse`.
4. Add further domain subdirectories after the matrix ownership cutover.
   **Done:** `Kernel/`, `Matrix/`, `Renderer/`, `Temporal/`, `Postprocess/`,
   `Weather/`, `Ssr/` and `Audio/` under `GxProofsGfx`.
