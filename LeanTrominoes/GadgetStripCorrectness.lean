/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripBoundary

/-!
# Correctness of blank-bordered strip substitution

On a normalized vertex-separated drawing with blank vertical boundary rows,
the Figure 11/12 gadget substitution has a strip tiling exactly when the
drawing has a trichromatic orientation.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- Exact correctness of horizontally periodic gadget substitution for a
normalized drawing whose vertical boundary rows are blank. -/
theorem periodicStrip_correct_of_normalized_blankBoundary
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated)
    (blankBoundary : drawing.HasBlankVerticalBoundary) :
    drawing.HasOrientation ↔
      PeriodicStripTrominoTiling tromino (drawing.periodicStrip tromino) := by
  constructor
  · intro hasOrientation
    have compatible := (behavior drawing separated).mp hasOrientation
    obtain ⟨assignment, locallyTiled, portCompatible⟩ := compatible.2
    exact ⟨drawing.periodicStrip_isWellFormed tromino,
      periodicStrip_tileable_of_portCompatible_blankBoundary tromino drawing
        assignment locallyTiled portCompatible blankBoundary⟩
  · rintro ⟨-, stripTileable⟩
    apply (periodicRegion_correct_of_normalized tromino behavior drawing
      wellFormed separated).mpr
    exact ⟨drawing.periodicRegion_fullRank tromino,
      periodicRegion_tileable_of_periodicStrip_tileable tromino drawing
        stripTileable⟩

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
