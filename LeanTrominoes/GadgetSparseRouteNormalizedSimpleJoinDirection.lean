/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteNormalizedJoinDirection
import LeanTrominoes.OrthogonalPolylineLoopErasureJoin

/-! # Direction words of normalized simple endpoint joins -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

/-- When two simple orthogonal routes meet only at their endpoint, whole-route
normalization leaves both direction words unchanged and concatenates them.
This is the stream boundary needed by the fallback retained-fan compiler: the
dynamic source prefix and the finite fan suffix may be emitted independently. -/
theorem
    unitSubdivisionDirections_normalizeOrthogonalPolyline_joinAtEndpoint_of_simple
    {first second : List Cell}
    {boundary : Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (firstSimple : LocalIncidenceDrawing.RouteIsSimple first)
    (secondSimple : LocalIncidenceDrawing.RouteIsSimple second)
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline first →
        point ∈ AxisDirection.unitSubdividePolyline second →
        point = boundary) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint first second)) =
      unitSubdivisionDirections first ++
        unitSubdivisionDirections second := by
  have normalizedEq :=
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_of_only_common
      firstNonempty secondNonempty firstOrthogonal secondOrthogonal
      secondSimple firstLast secondHead onlyCommon
  calc
    unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint first second)) =
        unitSubdivisionDirections
            (AxisDirection.normalizeOrthogonalPolyline first) ++
          unitSubdivisionDirections second :=
      unitSubdivisionDirections_normalized_join
        normalizedEq firstNonempty firstOrthogonal firstLast
        secondNonempty secondOrthogonal secondHead
    _ = unitSubdivisionDirections first ++
          unitSubdivisionDirections second := by
      rw [unitSubdivisionDirections_normalizeOrthogonalPolyline_of_simple
        firstNonempty firstOrthogonal firstSimple]

end Gadget
end LeanTrominoes

