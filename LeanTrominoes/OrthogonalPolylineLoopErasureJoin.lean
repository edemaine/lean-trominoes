/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListLoopEraseAppend
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin

/-!
# Loop erasure of endpoint joins

When an orthogonal prefix meets a simple orthogonal suffix only at their
unit-subdivided join boundary, normalization is confined to the prefix.  The
suffix is merely unit-subdivided and reattached unchanged.
-/

namespace LeanTrominoes
namespace AxisDirection

open PeriodicOrthocrossing

/-- Orthogonal loop erasure localizes to the possibly nonsimple prefix of an
endpoint join when the simple suffix has no other subdivided contact. -/
theorem normalizeOrthogonalPolyline_joinAtEndpoint_of_only_common
    {first second : List Cell}
    {boundary : Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (secondSimple : LocalIncidenceDrawing.RouteIsSimple second)
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (onlyCommon :
      ∀ point,
        point ∈ unitSubdividePolyline first →
        point ∈ unitSubdividePolyline second →
        point = boundary) :
    normalizeOrthogonalPolyline (joinAtEndpoint first second) =
      joinAtEndpoint
        (normalizeOrthogonalPolyline first)
        (unitSubdividePolyline second) := by
  have joinedNonempty : joinAtEndpoint first second ≠ [] := by
    intro joinedEmpty
    cases first with
    | nil => exact firstNonempty rfl
    | cons head tail =>
        simp [joinAtEndpoint] at joinedEmpty
  have joinedOrthogonal :
      OrthogonalPolyline (joinAtEndpoint first second) :=
    firstOrthogonal.joinAtEndpoint secondOrthogonal
      firstLast secondHead
  have subdividedSecondNodup :
      (unitSubdividePolyline second).Nodup :=
    unitSubdividePolyline_nodup secondOrthogonal secondSimple
  have subdividedSecondHead :
      (unitSubdividePolyline second).head? = some boundary := by
    rw [unitSubdividePolyline_head? secondNonempty, secondHead]
  rw [normalizeOrthogonalPolyline_eq_erase
      joinedNonempty joinedOrthogonal,
    eraseOrthogonalLoops_eq_listLoopErase
      joinedNonempty joinedOrthogonal,
    unitSubdividePolyline_joinAtEndpoint
      firstNonempty firstLast secondHead,
    Computability.listLoopErase_joinAtEndpoint_of_only_common
      (unitSubdividePolyline first)
      (unitSubdividePolyline second) boundary
      subdividedSecondHead subdividedSecondNodup onlyCommon,
    ← eraseOrthogonalLoops_eq_listLoopErase
      firstNonempty firstOrthogonal,
    ← normalizeOrthogonalPolyline_eq_erase
      firstNonempty firstOrthogonal]

end AxisDirection
end LeanTrominoes
