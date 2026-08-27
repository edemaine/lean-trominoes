/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionSteps

/-! # Finite direction words for unit-subdivided polylines -/

namespace LeanTrominoes
namespace Gadget

/-- Segment-major direction word of a unit-subdivided polyline. -/
def unitSubdivisionDirections : List Cell → List AxisDirection
  | first :: second :: rest =>
      List.replicate (AxisDirection.segmentLength first second)
          (AxisDirection.between first second) ++
        unitSubdivisionDirections (second :: rest)
  | _ => []
termination_by points => points.length

/-- Converting every subdivision direction to its unit step gives exactly
the previously verified coordinate-offset word. -/
@[simp]
theorem map_step_unitSubdivisionDirections (points : List Cell) :
    (unitSubdivisionDirections points).map AxisDirection.step =
      unitSubdivisionOffsets points := by
  induction points using List.twoStepInduction with
  | nil => simp [unitSubdivisionDirections, unitSubdivisionOffsets]
  | singleton point =>
      simp [unitSubdivisionDirections, unitSubdivisionOffsets]
  | cons_cons first second rest _ induction =>
      simp only [unitSubdivisionDirections, unitSubdivisionOffsets,
        List.map_append, List.map_replicate]
      rw [induction second]

end Gadget
end LeanTrominoes
