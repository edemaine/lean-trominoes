/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepJoin
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-! # Exact offset words for unit-subdivided polylines -/

namespace LeanTrominoes
namespace Gadget

/-- Repeated unit-offset blocks, one for each consecutive source segment. -/
def unitSubdivisionOffsets : List Cell → List Cell
  | first :: second :: rest =>
      List.replicate (AxisDirection.segmentLength first second)
          (AxisDirection.between first second).step ++
        unitSubdivisionOffsets (second :: rest)
  | _ => []
termination_by points => points.length

/-- Unit subdivision realizes exactly the segment-major repeated-offset word. -/
theorem routeStepOffsets_unitSubdividePolyline
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    routeStepOffsets (AxisDirection.unitSubdividePolyline points) =
      unitSubdivisionOffsets points := by
  induction points using List.twoStepInduction with
  | nil => simp [unitSubdivisionOffsets, routeStepOffsets]
  | singleton point => simp [unitSubdivisionOffsets, routeStepOffsets]
  | cons_cons first second rest _ induction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline (second :: rest))
      have common :
          (AxisDirection.unitSegmentPoints first second).getLast? =
            (AxisDirection.unitSubdividePolyline
              (second :: rest)).head? := by
        rw [AxisDirection.unitSegmentPoints_getLast? parts.1]
        simpa using (AxisDirection.unitSubdividePolyline_head?
          (points := second :: rest) (by simp)).symm
      rw [AxisDirection.unitSubdividePolyline]
      rw [routeStepOffsets_joinAtEndpoint _ _ common]
      rw [routeStepOffsets_unitSegmentPoints parts.1]
      rw [induction second parts.2]
      rw [unitSubdivisionOffsets]

end Gadget
end LeanTrominoes
