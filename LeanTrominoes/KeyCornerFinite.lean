/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyCornerVerticalDirect
import LeanTrominoes.KeyCornerVerticalReflected
import LeanTrominoes.KeyCornerRightDirect
import LeanTrominoes.KeyCornerRightReflected

/-! # Finite corner-matching certificates at reference period 96

The independent certificate modules split the first coordinate and check each
row directly in the kernel, without a native evaluation axiom.
-/

namespace LeanTrominoes.KeyCornerArithmetic

theorem vertical_finite :
    ∀ s : SquareSymmetry, ∀ x y : Fin 104,
      compatible 96 s ((x.val : Int) - 4, (y.val : Int) - 4) verticalOffsets →
        s = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (2, 99) := by
  intro s
  cases s
  · exact Certificates.vertical_identity
  · exact Certificates.vertical_rotate90
  · exact Certificates.vertical_rotate180
  · exact Certificates.vertical_rotate270
  · exact Certificates.vertical_reflectX
  · exact Certificates.vertical_reflectDiagonal
  · exact Certificates.vertical_reflectY
  · exact Certificates.vertical_reflectAntidiagonal

theorem right_finite :
    ∀ s : SquareSymmetry, ∀ x y : Fin 104,
      compatible 96 s ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        s = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro s
  cases s
  · exact Certificates.right_identity
  · exact Certificates.right_rotate90
  · exact Certificates.right_rotate180
  · exact Certificates.right_rotate270
  · exact Certificates.right_reflectX
  · exact Certificates.right_reflectDiagonal
  · exact Certificates.right_reflectY
  · exact Certificates.right_reflectAntidiagonal

end LeanTrominoes.KeyCornerArithmetic
