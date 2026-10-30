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

-- This module serves as the root of the `GxProofs` library.
-- Import modules here that should be built as part of the library.
--ai: Keep every core module reachable by the blocking proof gate.
import GxProofs.ViewportRoundtrip
import GxProofs.HaloInset
import GxProofs.PressRoute
import GxProofs.EditLock
import GxProofs.SoloRestore
import GxProofs.DockRestore
import GxProofs.AiInput
import GxProofs.RhiFbo
import GxProofs.DrawState
import GxProofs.GfxConstants
import GxProofs.ElementState
import GxProofs.GridLayout
import GxProofs.GridRectTransform
import GxProofs.ViewportMath
import GxProofs.RhiState
import GxProofs.RhiBatch
import GxProofs.RhiTex
import GxProofs.RhiBuf
import GxProofs.RhiProgramRegistry
import GxProofs.GLState
import GxProofs.ReflectFlags
import GxProofs.RhiTarget
import GxProofs.RhiStateScope
import GxProofs.ShaderActive
import GxProofs.RenderTextureLifecycle
import GxProofs.TAAHalton
--ai: stateful temporal contracts complement the individual Halton arithmetic lemmas.
import GxProofs.TemporalHistory
--ai: matrix snapshot provenance is separate from ping-pong validity.
import GxProofs.TemporalSnapshots
import GxProofs.CascadeSplits
import GxProofs.PoolAlloc
import GxProofs.BufferPool
import GxProofs.EventLog
import GxProofs.QualityPreset
import GxProofs.MainDataSwitch
import GxProofs.ModuleInfoConsistency
import GxProofs.EmissiveFill
import GxProofs.Random32
import GxProofs.DockMargins
import GxProofs.EffectSources
import GxProofs.FocusRing
import GxProofs.MatrixAccess
import GxProofs.PipelineOrder
import GxProofs.PointShadowFaces
import GxProofs.ResourceLifecycle
import GxProofs.ShadowVP
import GxProofs.TitleYield
import GxProofs.ToolsState
--ai: explicit preset overwrite confirmation gates user-initiated save commits.
import GxProofs.GfxPresetOverwrite
--ai: one-shot camera render/apply/capture/restore lifecycle for the GFX editor.
import GxProofs.GfxCameraRender
--ai: sparse light-slot removal/reuse and shared point-shadow storage ownership.
import GxProofs.GfxLightShadowSlots
--ai: conditional visible image sky routing and capture/LUT selector isolation.
import GxProofs.VisibleImageSky
--ai: production SSR auxiliary gates and explicitly separate optional-camera design policy.
import GxProofs.SsrCoverage
