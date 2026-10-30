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

/-
  gX — basic unit contracts for src/gxmath/convert.c.
  //ai: decimal source literals interpreted as exact real constants.

  Both directions of foot/inch/metre, Kelvin/Celsius and Celsius/Fahrenheit
  conversion round-trip. These are ideal identities, not IEEE error bounds
  or physical-input validation. SI-prefix dispatch and coordinate, sky,
  RGB/HSV, sRGB, audio and other conversions remain outside this module.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxMath.Units

def footToMeter (x : ℝ) : ℝ := 0.3048 * x
def inchToMeter (x : ℝ) : ℝ := 0.0254 * x
noncomputable def meterToFoot (x : ℝ) : ℝ := x / 0.3048
noncomputable def meterToInch (x : ℝ) : ℝ := x / 0.0254
def kelvinToCelsius (x : ℝ) : ℝ := x - 273.15
def celsiusToKelvin (x : ℝ) : ℝ := x + 273.15
noncomputable def celsiusToFahrenheit (x : ℝ) : ℝ := x * 9 / 5 + 32
noncomputable def fahrenheitToCelsius (x : ℝ) : ℝ := (x - 32) * 5 / 9

theorem foot_meter_foot (x : ℝ) : meterToFoot (footToMeter x) = x := by
  unfold meterToFoot footToMeter
  ring

theorem meter_foot_meter (x : ℝ) : footToMeter (meterToFoot x) = x := by
  unfold meterToFoot footToMeter
  ring

theorem inch_meter_inch (x : ℝ) : meterToInch (inchToMeter x) = x := by
  unfold meterToInch inchToMeter
  ring

theorem meter_inch_meter (x : ℝ) : inchToMeter (meterToInch x) = x := by
  unfold meterToInch inchToMeter
  ring

theorem foot_eq_twelve_inches (x : ℝ) : footToMeter x = inchToMeter (12 * x) := by
  unfold footToMeter inchToMeter
  ring

theorem kelvin_celsius_kelvin (x : ℝ) : celsiusToKelvin (kelvinToCelsius x) = x := by
  unfold celsiusToKelvin kelvinToCelsius
  ring

theorem celsius_kelvin_celsius (x : ℝ) : kelvinToCelsius (celsiusToKelvin x) = x := by
  unfold celsiusToKelvin kelvinToCelsius
  ring

theorem celsius_fahrenheit_celsius (x : ℝ) :
    fahrenheitToCelsius (celsiusToFahrenheit x) = x := by
  unfold fahrenheitToCelsius celsiusToFahrenheit
  ring

theorem fahrenheit_celsius_fahrenheit (x : ℝ) :
    celsiusToFahrenheit (fahrenheitToCelsius x) = x := by
  unfold fahrenheitToCelsius celsiusToFahrenheit
  ring

theorem freezing_celsius_kelvin : celsiusToKelvin 0 = 273.15 := by
  norm_num [celsiusToKelvin]

theorem freezing_celsius_fahrenheit : celsiusToFahrenheit 0 = 32 := by
  norm_num [celsiusToFahrenheit]

theorem boiling_celsius_fahrenheit : celsiusToFahrenheit 100 = 212 := by
  norm_num [celsiusToFahrenheit]

end GxMath.Units
