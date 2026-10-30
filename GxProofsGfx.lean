/-
  SPDX-License-Identifier: GPL-3.0-or-later
  Copyright (c) 2025-2026 lanttu, opencode

  This file is part of gX proofs.
  gX proofs is free software: you can redistribute it and/or modify it under
  the terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
  gX proofs is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
  FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
  details.
  You should have received a copy of the GNU General Public License along with
  gX proofs. If not, see <https://www.gnu.org/licenses/>.
-/

-- This module serves as the root of the `GxProofsGfx` library.
-- Import modules here that should be built as part of the library.
import GxProofsGfx.Matrix.MatrixTuple
import GxProofsGfx.Renderer.Affine
import GxProofsGfx.Renderer.Viewport
import GxProofsGfx.Renderer.Pillarbox
import GxProofsGfx.Renderer.Engage
import GxProofsGfx.Renderer.Snap
import GxProofsGfx.Renderer.CameraLimits
--ai: conditional contraction/error bounds for the bounded world-space water query.
import GxProofsGfx.Renderer.WaterHeight
--ai: transactional editor drag history: no-op, changed commit, undo/redo and redo invalidation.
import GxProofsGfx.Editor.DragHistory
import GxProofsGfx.Audio.Attenuation
import GxProofsGfx.Matrix.MatrixField
import GxProofsGfx.Kernel.MainDataRefresh
import GxProofsGfx.Kernel.MainDataReset
--ai: accepted/rejected WM resize synchronization and window-sized target reload state.
import GxProofsGfx.Kernel.WindowResize
import GxProofsGfx.Renderer.LightAccumulation
--ai: exact-real point attenuation and the positive-quadratic cluster cutoff.
import GxProofsGfx.Renderer.LightAttenuation
import GxProofsGfx.Renderer.ModelPicking
import GxProofsGfx.Renderer.ShadowContain
--ai: Previously orphaned modules belong to the same pinned Mathlib gate.
import GxProofsGfx.Audio.Envelope
import GxProofsGfx.Renderer.BehindCamera
--ai: explicit conversions between the flat field, clip and logical matrix models.
import GxProofsGfx.Matrix.MatrixBridge
import GxProofsGfx.Renderer.FrustumCull
import GxProofsGfx.Postprocess.LensflareGhost
import GxProofsGfx.Renderer.SunUV
import GxProofsGfx.Audio.SynthFilter
import GxProofsGfx.Renderer.TextwriterLayout
--ai: conditional label raster/quad/padding/top/UV contracts with native/GPU obligations explicit.
import GxProofsGfx.Renderer.LabelContracts
--ai: ideal reprojection and explicit hybrid bilinear footprint contracts.
import GxProofsGfx.Temporal.TemporalSampling
--ai: distinguish numeric-field order, physical struct layout and raw GL upload.
import GxProofsGfx.Temporal.TemporalMatrix
--ai: exact C cofactor inverse discharges the ideal camera inverse premise.
import GxProofsGfx.Temporal.CofactorInverse
--ai: residual and homogeneous margins supply conditional quantitative reprojection budgets.
import GxProofsGfx.Temporal.ReprojectionError
--ai: componentwise residual weights and camera columns preserve anisotropic error information.
import GxProofsGfx.Temporal.WeightedReprojection
--ai: depth/UV/jitter input sensitivity and conditional grid quantization contracts.
import GxProofsGfx.Temporal.DepthInputError
--ai: exact plane reflection geometry and conditional projective lookup correspondence.
import GxProofsGfx.Ssr.PlanarReflection
--ai: reflected orientation, LookAt cross-product axes and conditional projected winding.
import GxProofsGfx.Ssr.ReflectionHandedness
--ai: positive-w perspective winding and conditional near-plane clipped fan orientation.
import GxProofsGfx.Renderer.ProjectionClipping
--ai: shared GL cubemap face algebra and asymmetric negative-X witness.
import GxProofsGfx.Renderer.CubemapGeometry
--ai: radial depth decoding, strict shadow comparisons and supplied error margins.
import GxProofsGfx.Renderer.PointShadowDepth
--ai: ordered cascade boundaries and conditional fade/projection bounds.
import GxProofsGfx.Renderer.CsmContracts
--ai: current SSAO generator is GTAO; conditional reconstruction/horizon/blur contracts.
import GxProofsGfx.Postprocess.GtaoContracts
--ai: source-grounded SSGI tangent/normalization/fallback contracts with explicit radiance limits.
import GxProofsGfx.Postprocess.SsgiContracts
--ai: postprocess target/source denominator mismatch and conditional empty-chain contracts.
import GxProofsGfx.Postprocess.PostprocessContracts
--ai: repaired camera-relative weather bounds and bounded four-tap godray stride.
import GxProofsGfx.Weather.WeatherContracts
import GxProofsGfx.Weather.GodrayContracts
--ai: current glass opacity-one routing counterexample; conditional fresh-capture obligations.
import GxProofsGfx.Ssr.GlassCapture
--ai: exact owned-fixture witness separating actual-hit and box-exit probe rays.
import GxProofsGfx.Ssr.ProbeBoxExit
--ai: analytic ray/plane validity and off-plane mirror-camera parallax counterexample.
import GxProofsGfx.Ssr.SsrRayCoverage
