/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRasterizationCorrectness
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterization

/-!
# Reading back the rectangular strip raster
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- A valid row and column retrieve the corresponding strip assignment
lookup from the rectangular row-major list. -/
theorem PlanarPresentation.finalStripCellTypes_getD
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {horizontal vertical : Nat}
    (horizontalValid :
      horizontal < presentation.finalNormalizationPeriod)
    (verticalValid : vertical < presentation.finalStripHeight) :
    presentation.finalStripCellTypes.getD
        (vertical * presentation.finalNormalizationPeriod + horizontal)
        .blank =
      presentation.finalStripCellTypeAt (horizontal, vertical) := by
  unfold PlanarPresentation.finalStripCellTypes
  exact rowMajorList_getD _ _ _ _ horizontalValid verticalValid

/-- Reading the compiled strip drawing at a finite position is exactly the
rectangular assignment lookup at that row and column. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_get
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (position : presentation.stripNormalizedOrthogonalDrawing.Position) :
    presentation.stripNormalizedOrthogonalDrawing.get position =
      presentation.finalStripCellTypeAt
        ((position.1.val : Int), (position.2.val : Int)) := by
  have horizontalValid :
      position.1.val < presentation.finalNormalizationPeriod := by
    simpa only [presentation.stripNormalizedOrthogonalDrawing_periods.1] using
      position.1.isLt
  have verticalValid :
      position.2.val < presentation.finalStripHeight := by
    simpa only [presentation.stripNormalizedOrthogonalDrawing_periods.2] using
      position.2.isLt
  dsimp only [Gadget.PeriodicOrthogonalDrawing.get,
    PlanarPresentation.stripNormalizedOrthogonalDrawing]
  have oneLe : 1 ≤ presentation.finalNormalizationPeriod :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt presentation.finalNormalizationPeriod_pos)
  simp only [Nat.sub_add_cancel oneLe]
  exact presentation.finalStripCellTypes_getD
    horizontalValid verticalValid

end PeriodicThreeDM
end LeanTrominoes
