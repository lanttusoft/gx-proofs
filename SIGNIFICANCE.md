<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Proof significance

This is a gX-specific adaptation of the VibeMathed significance discipline.
It does **not** measure how famous a theorem is or how hard it was to prove.
It measures:

> How much does gX depend on this contract being true, and how costly is a
> false model or a source-mismatch?

The score is an editorial estimate from 0 to 100, assigned during review with
a one-line justification. It is **not** assigned by the proof or the prover,
and kernel-checked status does not raise it.

## Anchors

| Score | Meaning |
|---:|---|
| 100 | Matrix upload/layout convention, kernel boundary, or a contract whose failure invalidates broad camera/engine behavior |
| 85–90 | RHI state/lifetime, allocator/pool, kernel flags, input routing |
| 75–80 | Core gxmath matrix/physics/quaternion, temporal history, resource lifecycle |
| 60–70 | Projection/clipping, cubemap/CSM/point-shadow, reflection geometry |
| 45–55 | SSR/GTAO/SSGI/postprocess, weather, picking, audio |
| 25–35 | Labels/layout, easing, advisory visuals |
| 5–15 | Historical counterexamples and illustrative bounds |
| 0 | Reserved; not for “unknown” |

Defaults exist for unreviewed modules only as coarse bands. A reviewed entry
carries `significance`, `justification` and, where applicable, `source`,
`guard`, `gate`, `scope` and `gaps`.

## Rules

- Score the consequence of the contract, not the elegance or verification
  level of the proof.
- Ties are correct; do not manufacture precision.
- When torn between two values, take the lower one.
- A one-line justification must name the strongest reason.
- The coarse class `K/A/B/C` drives the required proof-evidence level; the
  0–100 score is for ranking and reporting. They are reviewed together but
  are not automatically derived from each other.
- Scores and evidence declarations are static catalog metadata. They do not
  replace `proof_audit.py`, kernel checking, or the native gates.
