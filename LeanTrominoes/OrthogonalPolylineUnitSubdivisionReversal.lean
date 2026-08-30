/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.OrthogonalPolylineNormalizationDirectionExtensionality

/-! # Reversal of ordered orthogonal unit subdivision -/

namespace LeanTrominoes
namespace AxisDirection

open PeriodicOrthocrossing

/-- Reversing an orthogonal polyline reverses its ordered unit subdivision. -/
theorem unitSubdividePolyline_reverse
    (points : List Cell)
    (orthogonal : OrthogonalPolyline points) :
    unitSubdividePolyline points.reverse =
      (unitSubdividePolyline points).reverse := by
  by_cases nonempty : points ≠ []
  · have reverseNonempty : points.reverse ≠ [] := by
      simpa using nonempty
    have subdividedNonempty : unitSubdividePolyline points ≠ [] :=
      unitSubdividePolyline_ne_nil nonempty
    have reverseOrthogonal : OrthogonalPolyline points.reverse :=
      orthogonal.reverse
    have firstUnitSteps :
        (unitSubdividePolyline points.reverse).IsChain IsUnitAxisStep :=
      unitSubdividePolyline_unitSteps reverseOrthogonal
    have secondUnitSteps :
        (unitSubdividePolyline points).reverse.IsChain IsUnitAxisStep :=
      by
        rw [List.isChain_reverse]
        exact (unitSubdividePolyline_unitSteps orthogonal).imp
          fun _ _ unit => unit.symm
    apply Gadget.route_eq_of_head?_eq_of_routeStepDirections_eq_of_unitSteps
      firstUnitSteps secondUnitSteps
    · rw [unitSubdividePolyline_head? reverseNonempty,
        List.head?_reverse, List.head?_reverse,
        unitSubdividePolyline_getLast? nonempty orthogonal]
    · rw [← Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
          (unitSubdividePolyline points.reverse) firstUnitSteps,
        ← Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
          (unitSubdividePolyline points).reverse secondUnitSteps,
        Gadget.unitSubdivisionDirections_unitSubdividePolyline
          points.reverse reverseOrthogonal,
        Gadget.unitSubdivisionDirections_reverse
          (unitSubdividePolyline points)
          (orthogonalPolyline_of_unitSteps
            (unitSubdividePolyline_unitSteps orthogonal)),
        Gadget.unitSubdivisionDirections_unitSubdividePolyline
          points orthogonal,
        Gadget.unitSubdivisionDirections_reverse points orthogonal]
  · have empty : points = [] := List.eq_nil_iff_forall_not_mem.mpr
      fun point member => nonempty
        (List.ne_nil_of_mem member)
    simp [empty]

end AxisDirection
end LeanTrominoes
