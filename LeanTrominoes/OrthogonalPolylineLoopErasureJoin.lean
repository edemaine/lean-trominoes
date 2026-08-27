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

/-- If an endpoint join is simple, the unit subdivisions of its two pieces
can meet only at the advertised boundary. -/
theorem unitSubdividePolyline_only_common_of_join_simple
    {first second : List Cell}
    {boundary : Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (joinedSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (joinAtEndpoint first second)) :
    ∀ point,
      point ∈ unitSubdividePolyline first →
      point ∈ unitSubdividePolyline second →
      point = boundary := by
  let firstSubdivided := unitSubdividePolyline first
  let secondSubdivided := unitSubdividePolyline second
  have joinedOrthogonal :
      OrthogonalPolyline (joinAtEndpoint first second) :=
    firstOrthogonal.joinAtEndpoint secondOrthogonal
      firstLast secondHead
  have joinedSubdividedNodup :
      (unitSubdividePolyline
        (joinAtEndpoint first second)).Nodup :=
    unitSubdividePolyline_nodup joinedOrthogonal joinedSimple
  have subdivisionEq :
      unitSubdividePolyline (joinAtEndpoint first second) =
        joinAtEndpoint firstSubdivided secondSubdivided := by
    simpa only [firstSubdivided, secondSubdivided] using
      unitSubdividePolyline_joinAtEndpoint
        firstNonempty firstLast secondHead
  have disjointTail :
      List.Disjoint firstSubdivided secondSubdivided.tail := by
    rw [subdivisionEq] at joinedSubdividedNodup
    unfold joinAtEndpoint at joinedSubdividedNodup
    have separated :=
      (List.nodup_append.mp joinedSubdividedNodup).2.2
    rw [List.disjoint_left]
    intro point firstMember secondMember
    exact separated point firstMember point secondMember rfl
  have secondSubdividedHead :
      secondSubdivided.head? = some boundary := by
    simpa only [secondSubdivided] using
      (unitSubdividePolyline_head? secondNonempty).trans secondHead
  intro point firstMember secondMember
  have firstMember' : point ∈ firstSubdivided := by
    simpa only [firstSubdivided] using firstMember
  have secondMember' : point ∈ secondSubdivided := by
    simpa only [secondSubdivided] using secondMember
  cases secondEq : secondSubdivided with
  | nil => simp [secondEq] at secondSubdividedHead
  | cons head tail =>
      have headEq : head = boundary := by
        simpa [secondEq] using secondSubdividedHead
      rw [secondEq] at secondMember'
      rcases List.mem_cons.mp secondMember' with pointHead | pointTail
      · exact pointHead.trans headEq
      · exact (disjointTail firstMember' (by
          simpa [secondEq] using pointTail)).elim

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
