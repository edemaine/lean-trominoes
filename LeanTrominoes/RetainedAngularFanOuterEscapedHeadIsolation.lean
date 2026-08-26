/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin
import LeanTrominoes.RetainedAngularFanOuterEscapedTailCardinalBounds

/-! # Source-head isolation for escaped outer routes

The cardinal 64-block source escape never returns to its gate, while the
complete tail lies strictly inward of that gate.  Thus unit subdivision of
the complete escaped route retains an isolated first endpoint.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

private theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail_orthogonal
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (lengthLarge : 2 ≤ length) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
        center (.compass port, length) slot) := by
  have lengthPositive : 0 < length := by omega
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (.compass port, length) := by
    simp [retainedTerminalFanOuterSourceEscapeLength,
      retainedTerminalFanOuterRadialLength,
      retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalInterfaceMultiplier]
    omega
  unfold retainedTerminalFanOuterCoordinatedEscapedCompleteTail
  exact
    (retainedTerminalFanOuterEscapedShiftedTail_orthogonal
      center (.compass port, length) slot).joinAtEndpoint
      (retainedTerminalFanOuterLocalRouteAt_orthogonal
        center (.compass port) slot)
      (retainedTerminalFanOuterEscapedShiftedTail_getLast?
        center (.compass port, length) slot
        lengthPositive escapeFits)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center (.compass port) slot)

private theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail_unit_linear_upper
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          center (.compass port, length) slot)) :
    Cell.linearValue port.unitVector point ≤
      Cell.linearValue port.unitVector
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate -
        retainedTerminalFanOuterSourceEscapeLength := by
  let tail :=
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail
      center (.compass port, length) slot
  have tailOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline tail :=
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail_orthogonal
      center port length slot lengthLarge
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        tailOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact
      retainedTerminalFanOuterCoordinatedEscapedCompleteTail_cardinal_linear_upper
        center port length slot cardinal lengthLarge point originalMember
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    apply Cell.linearValue_le_of_segment_contains port.unitVector
      (Cell.linearValue port.unitVector
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate -
        retainedTerminalFanOuterSourceEscapeLength)
    · exact
        retainedTerminalFanOuterCoordinatedEscapedCompleteTail_cardinal_linear_upper
          center port length slot cardinal lengthLarge
          segment.start endpoints.1
    · exact
        retainedTerminalFanOuterCoordinatedEscapedCompleteTail_cardinal_linear_upper
          center port length slot cardinal lengthLarge
          segment.finish endpoints.2
    · exact GridSegment.contains_of_interiorContains interior

/-- Unit subdivision of a cardinal escaped outer route does not repeat its
source gate. -/
theorem retainedTerminalFanOuterEscapedCompleteRoute_headNotInTail
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterEscapedCompleteRoute
          center (.compass port, length) slot)) := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let escape :=
    (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
      center terminal slot).route
  let tail :=
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail
      center terminal slot
  have escapePair : escape = [gate, escapePoint] := by
    unfold escape
    simp only [retainedTerminalFanOuterRasterizedSourceEscapeCertificate]
    change
      compassRay (oppositePort port)
          retainedTerminalFanOuterSourceEscapeLength gate =
        [gate, escapePoint]
    rw [compassRay_eq_pair_of_cardinal]
    · unfold escapePoint
      rfl
    · simp [retainedTerminalFanOuterSourceEscapeLength]
    · rcases cardinal with rfl | rfl | rfl | rfl <;>
        simp [oppositePort]
  have escapeAligned :
      (GridSegment.mk gate escapePoint).IsAxisAligned := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [gate, escapePoint, terminal,
        retainedTerminalFanOuterSourceEscapePoint,
        retainedTerminalFanOuterSourceEscapeRay,
        retainedTerminalFanOuterInwardRayOfLength,
        retainedTerminalFanOuterSourceEscapeLength,
        RetainedRay.vector, oppositePort, Port.unitVector,
        Cell.add, Cell.scale, GridSegment.IsAxisAligned,
        GridSegment.IsHorizontal, GridSegment.IsVertical]
  have escapeFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline escape) := by
    rw [escapePair]
    simp only [AxisDirection.unitSubdividePolyline, joinAtEndpoint,
      List.tail_cons, List.append_nil]
    exact AxisDirection.headNotInTail_of_nodup
      (AxisDirection.unitSegmentPoints_nodup escapeAligned)
  have gateNotInTail :
      gate ∉ AxisDirection.unitSubdividePolyline tail := by
    intro gateMember
    have bound :=
      retainedTerminalFanOuterCoordinatedEscapedCompleteTail_unit_linear_upper
        center port length slot cardinal lengthLarge gate gateMember
    simp [gate, terminal,
      retainedTerminalFanOuterSourceEscapeLength] at bound
  rw [
    retainedTerminalFanOuterEscapedCompleteRoute_eq_coordinatedRasterized,
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
  apply escapeFresh.unitSubdividePolyline_joinAtEndpoint
  · rw [escapePair]
    simp
  · rw [escapePair]
    rfl
  · rw [escapePair]
    rfl
  · exact
      retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        center terminal slot
  · exact gateNotInTail

end PeriodicEightOccurrenceSplit
end LeanTrominoes
