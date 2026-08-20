/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripSubstitution
import LeanTrominoes.PeriodicStripFlatEncoding

/-! # Explicit flat fields of gadget-substituted strips -/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- Flat natural fields written directly from the natural-range expanded
gadget motif. -/
def computablePeriodicStripFields (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : List Nat :=
  let motif := drawing.computableExpandedMotif tromino
  [6 * drawing.verticalPeriod, 6 * drawing.horizontalPeriod, motif.length] ++
    motif.flatMap PeriodicStripFlatEncoding.cellFields

theorem computablePeriodicStripFields_eq (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    drawing.computablePeriodicStripFields tromino =
      let motif := drawing.computableExpandedMotif tromino
      [6 * drawing.verticalPeriod, 6 * drawing.horizontalPeriod,
        motif.length] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields :=
  rfl

/-- The direct field layout is definitionally the flat encoding payload of
the computable periodic strip. -/
theorem stripFields_computablePeriodicStrip (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    PeriodicStripFlatEncoding.stripFields
        (drawing.computablePeriodicStrip tromino) =
      drawing.computablePeriodicStripFields tromino := by
  rfl

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
