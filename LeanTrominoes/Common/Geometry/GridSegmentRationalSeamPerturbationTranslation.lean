/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalSeamPerturbationGeometry

/-! # Rational seam perturbations commute with integer-cell translations -/
namespace LeanTrominoes
namespace GridSegment

theorem horizontalSeamVelocity_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).horizontalSeamVelocity = segment.horizontalSeamVelocity := by
  simp [horizontalSeamVelocity,translate,Cell.add]

theorem rationalAbscissaAt_translate (segment : GridSegment) (offset : Cell) (height : ℚ) :
    (segment.translate offset).rationalAbscissaAt (height+offset.2) = segment.rationalAbscissaAt height+offset.1 := by
  simp [rationalAbscissaAt,translate,Cell.add]
  ring

end GridSegment
namespace OrthogonalDrawingRefinement

theorem rationalSlabMargin_translate (coordinate velocity : ℚ) (shift : Int) :
    rationalSlabMargin (coordinate+shift) velocity = rationalSlabMargin coordinate velocity := by
  unfold rationalSlabMargin
  rw [Int.floor_add_intCast]
  push_cast
  have integral : coordinate+(shift : ℚ) = (⌊coordinate⌋ : ℚ)+shift ↔ coordinate = (⌊coordinate⌋ : ℚ) := by
    constructor <;> intro equal <;> linarith
  have leftGap : coordinate+(shift : ℚ)-((⌊coordinate⌋ : ℚ)+shift) = coordinate-(⌊coordinate⌋ : ℚ) := by ring
  have rightGap : (⌊coordinate⌋ : ℚ)+(shift : ℚ)+1-(coordinate+shift) = (⌊coordinate⌋ : ℚ)+1-coordinate := by ring
  simp only [integral,leftGap,rightGap]

theorem rationalSlabMargin_residue (period : Int) (coordinate velocity : ℚ) :
    rationalSlabMargin coordinate velocity = rationalSlabMargin (rationalResidue period coordinate) velocity := by
  have decomposition : coordinate = rationalResidue period coordinate+((period*rationalCell period coordinate : Int) : ℚ) := by
    calc coordinate = (period : ℚ)*rationalCell period coordinate+rationalResidue period coordinate := rationalCoordinate_decomposition _ _
         _ = _ := by push_cast; ring
  calc rationalSlabMargin coordinate velocity =
      rationalSlabMargin (rationalResidue period coordinate+((period*rationalCell period coordinate : Int) : ℚ)) velocity :=
        congrArg (fun point => rationalSlabMargin point velocity) decomposition
       _ = _ := rationalSlabMargin_translate _ _ _

end OrthogonalDrawingRefinement
end LeanTrominoes
