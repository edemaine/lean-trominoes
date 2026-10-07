/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealHalfStep
import LeanTrominoes.GridPolylineRealSimpleEndpointIndices
import LeanTrominoes.OrthogonalPolylineSymmetries
import LeanTrominoes.GridPolylineRealAlgebra

/-! # Distinct endpoint rays for simple orthogonal loops -/
namespace LeanTrominoes.GridPolyline

theorem realHalfStep_not_endpoint (route : List Cell) (anchor : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) : ¬ RealIsEndpoint route (realHalfStep anchor direction) := by
  rintro (⟨endpoint,_,equal⟩ | ⟨endpoint,_,equal⟩) <;> exact realHalfStep_not_integral anchor genuine endpoint equal

theorem firstDirection_of_first_two {route : List Cell} {first second : Cell}
    (firstAt : route[0]? = some first) (secondAt : route[1]? = some second) :
    AxisDirection.polylineFirstDirection route = AxisDirection.between first second := by
  cases route with
  | nil => simp at firstAt
  | cons a rest =>
    cases rest with
    | nil => simp at secondAt
    | cons b rest =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at firstAt
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at secondAt
      subst a
      subst b
      rfl

theorem firstDirection_of_indexed_first {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments route).zipIdx) (first : tagged.2 = 0) :
    AxisDirection.polylineFirstDirection route = AxisDirection.between tagged.1.start tagged.1.finish := by
  have ends := indexed_gridPolylineSegment_endpoints member
  rw [first] at ends
  exact firstDirection_of_first_two ends.1 ends.2

theorem lastDirection_of_indexed_last {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (last : tagged.2+1 = (gridPolylineSegments route).length) (aligned : tagged.1.IsAxisAligned) :
    AxisDirection.polylineLastDirection route = AxisDirection.between tagged.1.start tagged.1.finish := by
  have valid := List.snd_lt_of_mem_zipIdx member
  have count := gridPolylineSegments_length route
  have long : 2 ≤ route.length := by omega
  have ends := indexed_gridPolylineSegment_endpoints member
  have firstAt : route.reverse[0]? = some tagged.1.finish := by
    rw [List.getElem?_reverse (by omega : 0 < route.length)]
    have indexEq : route.length-1-0 = tagged.2+1 := by omega
    rw [indexEq]
    exact ends.2
  have secondAt : route.reverse[1]? = some tagged.1.start := by
    rw [List.getElem?_reverse (by omega : 1 < route.length)]
    have indexEq : route.length-1-1 = tagged.2 := by omega
    rw [indexEq]
    exact ends.1
  unfold AxisDirection.polylineLastDirection
  rw [firstDirection_of_first_two firstAt secondAt,
    AxisDirection.between_reverse_eq_opposite (AxisDirection.between_isGenuine_of_axisAligned aligned),
    AxisDirection.opposite_opposite]

theorem IsRealSimple.closed_segment_count {route : List Cell} (simple : IsRealSimple route) {anchor : Cell}
    (head : route.head? = some anchor) (last : route.getLast? = some anchor) :
    2 ≤ (gridPolylineSegments route).length := by
  cases route with
  | nil => simp at head
  | cons first rest =>
    cases rest with
    | nil => have long := simple.1; simp at long
    | cons second rest =>
      cases rest with
      | nil =>
        have same : first = second := by simpa using (Option.some.inj head).trans (Option.some.inj last).symm
        exact (simple.2.1 ⟨first,second⟩ (by simp [gridPolylineSegments]) same).elim
      | cons third rest => simp [gridPolylineSegments]

theorem IsRealSimple.closed_endpoint_directions_ne {route : List Cell} (simple : IsRealSimple route)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route) {anchor : Cell}
    (head : route.head? = some anchor) (last : route.getLast? = some anchor) :
    AxisDirection.polylineFirstDirection route ≠ (AxisDirection.polylineLastDirection route).opposite := by
  intro equal
  have count := simple.closed_segment_count head last
  let firstPiece := (gridPolylineSegments route)[0]'(by omega)
  let lastIndex := (gridPolylineSegments route).length-1
  have lastValid : lastIndex < (gridPolylineSegments route).length := by dsimp [lastIndex]; omega
  let lastPiece := (gridPolylineSegments route)[lastIndex]'lastValid
  have firstMember : (firstPiece,0) ∈ (gridPolylineSegments route).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem (by omega : 0 < (gridPolylineSegments route).length)]
  have lastMember : (lastPiece,lastIndex) ∈ (gridPolylineSegments route).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem lastValid]
  have lastAt : lastIndex+1 = (gridPolylineSegments route).length := by dsimp [lastIndex]; omega
  have source : firstPiece.start = anchor := Option.some.inj
    ((indexed_gridPolylineSegment_head firstMember rfl).symm.trans head)
  have target : lastPiece.finish = anchor := Option.some.inj
    ((indexed_gridPolylineSegment_last lastMember lastAt).symm.trans last)
  have firstAligned := (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mp orthogonal _
    (List.fst_mem_of_mem_zipIdx firstMember)
  have lastAligned := (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mp orthogonal _
    (List.fst_mem_of_mem_zipIdx lastMember)
  have firstDirection := firstDirection_of_indexed_first firstMember rfl
  have lastDirection := lastDirection_of_indexed_last lastMember lastAt lastAligned
  dsimp only [Prod.fst] at firstAligned lastAligned firstDirection lastDirection
  have firstContains := GridSegment.realContains_halfStep firstAligned
  have lastReverseAligned : lastPiece.reverse.IsAxisAligned :=
    (GridSegment.isAxisAligned_swap lastPiece.start lastPiece.finish).mp lastAligned
  have lastContains := GridSegment.realContains_halfStep lastReverseAligned
  have reverseDirection : AxisDirection.between lastPiece.finish lastPiece.start =
      (AxisDirection.between lastPiece.start lastPiece.finish).opposite :=
    AxisDirection.between_reverse_eq_opposite (AxisDirection.between_isGenuine_of_axisAligned
      (first := lastPiece.start) (second := lastPiece.finish) lastAligned)
  simp only [GridSegment.reverse] at lastContains
  rw [reverseDirection,← lastDirection,← equal] at lastContains
  rw [← firstDirection,source] at firstContains
  have lastActual := (GridSegment.realContains_reverse lastPiece _).mp lastContains
  rw [target] at lastActual
  have contact := simple.2.2 (firstPiece,0) firstMember (lastPiece,lastIndex) lastMember (by dsimp [lastIndex]; omega)
    (realHalfStep anchor (AxisDirection.polylineFirstDirection route)) firstContains lastActual
  have genuine : (AxisDirection.polylineFirstDirection route).IsGenuine := by
    rw [firstDirection]
    exact AxisDirection.between_isGenuine_of_axisAligned firstAligned
  rcases contact with adjacent | closed
  · exact (realHalfStep_not_integral anchor genuine firstPiece.finish adjacent.2).elim
  · exact (realHalfStep_not_integral anchor genuine firstPiece.start closed.2.2.1).elim

theorem realContains_halfStep_at_last_outward {route : List Cell} {last : Cell}
    (long : 2 ≤ route.length) (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (atLast : route.getLast? = some last) :
    RealContains route (realHalfStep last (AxisDirection.polylineLastDirection route).opposite) := by
  have reversedHead : route.reverse.head? = some last := by simpa only [List.head?_reverse] using atLast
  have reversedContains := realContains_halfStep_at_head (by simpa using long) orthogonal.reverse reversedHead
  apply (realContains_reverse _ _).mp
  simpa only [AxisDirection.polylineLastDirection,AxisDirection.opposite_opposite] using reversedContains

end LeanTrominoes.GridPolyline
