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
  gxmath/MatrixSmall.lean
  gX — a game engine

  Formal contracts for the 2×2/3×3 determinant and trace helpers added to
  src/gxmath/matrix.c.

  Field names follow the logical row-major interpretation used by the C
  helpers (m0..m3 / m0..m8). The physical C structs are column-major; the
  named-field access in matrix.c is the correspondence point. The formal
  math is over ℝ and does not certify IEEE Float execution.

  Theorems proven:
    - det2/trace2 and det3/trace3 identities
    - diagonal-matrix determinants
    - transpose invariance for both sizes
    - scalar-scaling laws for both determinants
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GxMath
namespace MatrixSmall

structure Mat2 where
  m0 : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ

def identity2 : Mat2 :=
  { m0 := 1, m1 := 0, m2 := 0, m3 := 1 }

def diag2 (a b : ℝ) : Mat2 :=
  { m0 := a, m1 := 0, m2 := 0, m3 := b }

def transpose2 (m : Mat2) : Mat2 :=
  { m0 := m.m0, m1 := m.m2, m2 := m.m1, m3 := m.m3 }

def scale2 (s : ℝ) (m : Mat2) : Mat2 :=
  { m0 := s * m.m0, m1 := s * m.m1,
    m2 := s * m.m2, m3 := s * m.m3 }

def det2 (m : Mat2) : ℝ :=
  m.m0 * m.m3 - m.m1 * m.m2

def trace2 (m : Mat2) : ℝ :=
  m.m0 + m.m3

theorem det2_identity : det2 identity2 = 1 := by
  norm_num [det2, identity2]

theorem trace2_identity : trace2 identity2 = 2 := by
  norm_num [trace2, identity2]

theorem det2_diag (a b : ℝ) : det2 (diag2 a b) = a * b := by
  simp [det2, diag2]

theorem det2_transpose (m : Mat2) : det2 (transpose2 m) = det2 m := by
  simp [det2, transpose2]
  ring

theorem trace2_transpose (m : Mat2) : trace2 (transpose2 m) = trace2 m := by
  simp [trace2, transpose2]

theorem det2_scale (s : ℝ) (m : Mat2) :
    det2 (scale2 s m) = s ^ 2 * det2 m := by
  simp [det2, scale2]
  ring

structure Mat3 where
  m0 : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ
  m4 : ℝ
  m5 : ℝ
  m6 : ℝ
  m7 : ℝ
  m8 : ℝ

def identity3 : Mat3 :=
  { m0 := 1, m1 := 0, m2 := 0,
    m3 := 0, m4 := 1, m5 := 0,
    m6 := 0, m7 := 0, m8 := 1 }

def diag3 (a b c : ℝ) : Mat3 :=
  { m0 := a, m1 := 0, m2 := 0,
    m3 := 0, m4 := b, m5 := 0,
    m6 := 0, m7 := 0, m8 := c }

def transpose3 (m : Mat3) : Mat3 :=
  { m0 := m.m0, m1 := m.m3, m2 := m.m6,
    m3 := m.m1, m4 := m.m4, m5 := m.m7,
    m6 := m.m2, m7 := m.m5, m8 := m.m8 }

def scale3 (s : ℝ) (m : Mat3) : Mat3 :=
  { m0 := s * m.m0, m1 := s * m.m1, m2 := s * m.m2,
    m3 := s * m.m3, m4 := s * m.m4, m5 := s * m.m5,
    m6 := s * m.m6, m7 := s * m.m7, m8 := s * m.m8 }

def det3 (m : Mat3) : ℝ :=
  m.m0 * (m.m4 * m.m8 - m.m5 * m.m7)
  - m.m1 * (m.m3 * m.m8 - m.m5 * m.m6)
  + m.m2 * (m.m3 * m.m7 - m.m4 * m.m6)

def trace3 (m : Mat3) : ℝ :=
  m.m0 + m.m4 + m.m8

theorem det3_identity : det3 identity3 = 1 := by
  norm_num [det3, identity3]

theorem trace3_identity : trace3 identity3 = 3 := by
  norm_num [trace3, identity3]

theorem det3_diag (a b c : ℝ) : det3 (diag3 a b c) = a * b * c := by
  simp [det3, diag3]
  ring

theorem det3_transpose (m : Mat3) : det3 (transpose3 m) = det3 m := by
  simp [det3, transpose3]
  ring

theorem trace3_transpose (m : Mat3) : trace3 (transpose3 m) = trace3 m := by
  simp [trace3, transpose3]

theorem det3_scale (s : ℝ) (m : Mat3) :
    det3 (scale3 s m) = s ^ 3 * det3 m := by
  simp [det3, scale3]
  ring

end MatrixSmall
end GxMath
