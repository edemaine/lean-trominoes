import LeanTrominoes.OrthogonalDrawing
import LeanTrominoes.Periodic
import Mathlib.Data.List.FinRange

/-!
# Substitution of normalized drawing cells by tromino gadgets

Each cell of a normalized drawing is replaced by its `6 × 6` Figure 11 or 12
pixel mask.  This file defines the finite motif produced by that substitution
and packages it as the periodic-region input of Theorem 5.2.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- The positive horizontal period of the finite drawing domain. -/
def horizontalPeriod (drawing : PeriodicOrthogonalDrawing) : Nat :=
  drawing.horizontalPeriodPred + 1

/-- The positive vertical period of the finite drawing domain. -/
def verticalPeriod (drawing : PeriodicOrthogonalDrawing) : Nat :=
  drawing.verticalPeriodPred + 1

/-- Origin of a `6 × 6` gadget block in the expanded motif. -/
def blockOrigin (horizontal vertical : Nat) : Cell :=
  (6 * (horizontal : Int), 6 * (vertical : Int))

/-- Translate every local paper pixel into one block of the expanded motif. -/
def expandedBlockPixels (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) :
    List Cell :=
  (orthogonalCellPixels tromino (drawing.get position)).map fun pixel =>
    Cell.add (blockOrigin position.1.val position.2.val) pixel

/-- The finite motif obtained by substituting every drawing cell with its
Figure 11 or 12 gadget. -/
def expandedMotif (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : List Cell :=
  (List.finRange drawing.horizontalPeriod).flatMap fun horizontal =>
    (List.finRange drawing.verticalPeriod).flatMap fun vertical =>
      expandedBlockPixels tromino drawing (horizontal, vertical)

/-- Compile a normalized periodic drawing to the periodic subset tiled in the
hardness reduction. -/
def periodicRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : PeriodicRegion where
  motif := expandedMotif tromino drawing
  period₁ := (6 * (drawing.horizontalPeriod : Int), 0)
  period₂ := (0, 6 * (drawing.verticalPeriod : Int))

theorem periodicRegion_determinant (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicRegion tromino).determinant =
      36 * (drawing.horizontalPeriod : Int) *
        (drawing.verticalPeriod : Int) := by
  simp [periodicRegion, PeriodicRegion.determinant]
  ring

/-- The compiled region always has two independent period vectors. -/
theorem periodicRegion_fullRank (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicRegion tromino).IsFullRank := by
  rw [PeriodicRegion.IsFullRank, periodicRegion_determinant]
  have horizontalPositive : (0 : Int) < drawing.horizontalPeriod := by
    simp [horizontalPeriod]
  have verticalPositive : (0 : Int) < drawing.verticalPeriod := by
    simp [verticalPeriod]
  positivity

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
