/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PeriodicGridDrawingEndpointContacts

/-!
# Extracting separated lifted routes from a periodic drawing

A ribbon-ready periodic drawing describes separation through globally
indexed segment and point occurrences.  Ribbon subdivision is more
conveniently phrased using the finite two-route predicate from local embedded
drawings.  This file bridges the two interfaces for any pair of distinct
lifted route occurrences.
-/

namespace LeanTrominoes

namespace GridSegment

/-- Either endpoint of an axis-aligned segment is contained in the closed
segment. -/
theorem contains_start_of_axisAligned
    {segment : GridSegment}
    (aligned : segment.IsAxisAligned) :
    segment.Contains segment.start := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [IsAxisAligned, IsHorizontal, IsVertical] at aligned
  unfold Contains
  rcases aligned with horizontal | vertical
  · left
    refine ⟨horizontal, rfl, ?_⟩
    rcases le_total startX finishX with forward | backward
    · exact Or.inl ⟨le_rfl, forward⟩
    · exact Or.inr ⟨backward, le_rfl⟩
  · right
    refine ⟨vertical, rfl, ?_⟩
    rcases le_total startY finishY with forward | backward
    · exact Or.inl ⟨le_rfl, forward⟩
    · exact Or.inr ⟨backward, le_rfl⟩

theorem contains_finish_of_axisAligned
    {segment : GridSegment}
    (aligned : segment.IsAxisAligned) :
    segment.Contains segment.finish := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [IsAxisAligned, IsHorizontal, IsVertical] at aligned
  unfold Contains
  rcases aligned with horizontal | vertical
  · left
    refine ⟨horizontal, horizontal.1.symm, ?_⟩
    rcases le_total startX finishX with forward | backward
    · exact Or.inl ⟨forward, le_rfl⟩
    · exact Or.inr ⟨le_rfl, backward⟩
  · right
    refine ⟨vertical, vertical.1.symm, ?_⟩
    rcases le_total startY finishY with forward | backward
    · exact Or.inl ⟨forward, le_rfl⟩
    · exact Or.inr ⟨le_rfl, backward⟩

end GridSegment

namespace PeriodicOrthocrossing

/-- Every listed point of a nondegenerate orthogonal polyline lies on at
least one of its segments. -/
theorem exists_segment_contains_of_mem
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal : OrthogonalPolyline points)
    {point : Cell} (pointMember : point ∈ points) :
    ∃ segment ∈ gridPolylineSegments points,
      segment.Contains point := by
  induction points using List.twoStepInduction with
  | nil =>
      simp at length
  | singleton only =>
      simp at length
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            OrthogonalPolyline (second :: rest))
      simp only [List.mem_cons] at pointMember
      rcases pointMember with pointFirst | pointTail
      · subst point
        exact
          ⟨GridSegment.mk first second, by
            simp [gridPolylineSegments],
            GridSegment.contains_start_of_axisAligned parts.1⟩
      · cases rest with
        | nil =>
            simp at pointTail
            subst point
            exact
              ⟨GridSegment.mk first second, by
                simp [gridPolylineSegments],
                GridSegment.contains_finish_of_axisAligned parts.1⟩
        | cons third rest =>
            rcases
                tailInduction second (by simp) parts.2
                  (by simpa only [List.mem_cons] using pointTail) with
              ⟨segment, segmentMember, contains⟩
            exact
              ⟨segment, by
                exact List.mem_cons_of_mem _ segmentMember,
                contains⟩

end PeriodicOrthocrossing

namespace PeriodicGridDrawing

/-- A route-local segment index gives a member of the drawing's global
indexed-segment enumeration. -/
theorem indexedSegment_mem_of_route_mem
    {drawing : PeriodicGridDrawing}
    {route : List Cell} {routeIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx)
    (segmentIndex : Fin (gridPolylineSegments route).length) :
    (⟨routeIndex, segmentIndex,
        (gridPolylineSegments route).get segmentIndex⟩ :
      IndexedGridSegment) ∈ drawing.indexedSegments := by
  unfold indexedSegments
  apply List.mem_flatMap.mpr
  refine ⟨(route, routeIndex), routeMember, ?_⟩
  apply List.mem_map.mpr
  refine
    ⟨((gridPolylineSegments route).get segmentIndex,
        segmentIndex.val), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  exact ⟨segmentIndex.isLt, by simp⟩

/-- A route-local point index gives a member of the drawing's global
indexed-route-point enumeration. -/
theorem indexedRoutePoint_mem_of_route_mem
    {drawing : PeriodicGridDrawing}
    {route : List Cell} {routeIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx)
    (pointIndex : Fin route.length) :
    ({ routeIndex := routeIndex
       pointIndex := pointIndex
       routeLength := route.length
       point := route.get pointIndex } :
      IndexedRoutePoint) ∈ drawing.indexedRoutePoints := by
  unfold indexedRoutePoints
  apply List.mem_flatMap.mpr
  refine ⟨(route, routeIndex), routeMember, ?_⟩
  apply List.mem_map.mpr
  refine
    ⟨(route.get pointIndex, pointIndex.val), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  exact ⟨pointIndex.isLt, by simp⟩

private theorem segmentOccurrenceKey_ne_of_routeOccurrence_ne
    {firstRouteIndex secondRouteIndex : Nat}
    {firstSegmentIndex secondSegmentIndex : Nat}
    {firstSegment secondSegment : GridSegment}
    {firstTranslate secondTranslate : Cell}
    (different :
      (firstRouteIndex, firstTranslate) ≠
        (secondRouteIndex, secondTranslate)) :
    SegmentOccurrenceKey
        ⟨firstRouteIndex, firstSegmentIndex, firstSegment⟩
        firstTranslate ≠
      SegmentOccurrenceKey
        ⟨secondRouteIndex, secondSegmentIndex, secondSegment⟩
        secondTranslate := by
  intro equal
  apply different
  simp only [SegmentOccurrenceKey, Prod.mk.injEq] at equal ⊢
  exact ⟨equal.1, equal.2.2⟩

private theorem routePointOccurrenceKey_ne_of_routeOccurrence_ne
    {firstRouteIndex secondRouteIndex : Nat}
    {firstPointIndex secondPointIndex : Nat}
    {firstTranslate secondTranslate : Cell}
    (different :
      (firstRouteIndex, firstTranslate) ≠
        (secondRouteIndex, secondTranslate)) :
    RoutePointOccurrenceKey
        { routeIndex := firstRouteIndex
          pointIndex := firstPointIndex
          routeLength := 0
          point := (0, 0) }
        firstTranslate ≠
      RoutePointOccurrenceKey
        { routeIndex := secondRouteIndex
          pointIndex := secondPointIndex
          routeLength := 0
          point := (0, 0) }
        secondTranslate := by
  intro equal
  apply different
  simp only [RoutePointOccurrenceKey, Prod.mk.injEq] at equal ⊢
  exact ⟨equal.1, equal.2.2⟩

/-- A first-or-last numeric point index gives the corresponding finite-route
endpoint predicate. -/
theorem routePointIsEndpoint_of_index
    {route : List Cell} (index : Fin route.length)
    (outer :
      index.val = 0 ∨ index.val + 1 = route.length) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
      route (route.get index) := by
  rcases outer with first | last
  · left
    cases route with
    | nil => exact Fin.elim0 index
    | cons head tail =>
        have indexEqual :
            index = ⟨0, by simp⟩ :=
          Fin.ext first
        subst index
        simp
  · right
    have nonempty : route ≠ [] := by
      intro empty
      subst route
      exact Fin.elim0 index
    have lastIndexLt :
        route.length - 1 < route.length := by
      omega
    let lastIndex : Fin route.length :=
      ⟨route.length - 1, lastIndexLt⟩
    have indexEqual : lastIndex = index := by
      apply Fin.ext
      simp [lastIndex]
      omega
    have getEqual :
        route.get lastIndex = route.get index :=
      congrArg (List.get route) indexEqual
    have lastEqual :
        route.getLast nonempty = route.get index := by
      rw [← List.get_length_sub_one lastIndexLt]
      exact getEqual
    rw [List.getLast?_eq_getLast_of_ne_nil nonempty,
      lastEqual]

/-- Any two distinct lifted occurrences in a continuously planar,
endpoint-contact-certified orthogonal drawing satisfy the finite complete
route-separation predicate. -/
theorem routeOccurrences_avoidEachOther
    {drawing : PeriodicGridDrawing}
    (continuous : drawing.IsContinuouslyPlanar)
    (endpointContacts :
      drawing.RoutePointsMeetOnlyAtEndpoints)
    {first second : List Cell}
    {firstRouteIndex secondRouteIndex : Nat}
    (firstRouteMember :
      (first, firstRouteIndex) ∈ drawing.edgeRoutes.zipIdx)
    (secondRouteMember :
      (second, secondRouteIndex) ∈ drawing.edgeRoutes.zipIdx)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (firstTranslate secondTranslate : Cell)
    (occurrencesDifferent :
      (firstRouteIndex, firstTranslate) ≠
        (secondRouteIndex, secondTranslate)) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (first.map
        (Cell.add (drawing.periodTranslation firstTranslate)))
      (second.map
        (Cell.add (drawing.periodTranslation secondTranslate))) := by
  let firstOffset := drawing.periodTranslation firstTranslate
  let secondOffset := drawing.periodTranslation secondTranslate
  unfold
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex
    let firstOriginalIndex :
        Fin (gridPolylineSegments first).length :=
      ⟨firstIndex, by
        simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using firstIndex.isLt⟩
    let secondOriginalIndex :
        Fin (gridPolylineSegments second).length :=
      ⟨secondIndex, by
        simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using secondIndex.isLt⟩
    let firstIndexed : IndexedGridSegment :=
      ⟨firstRouteIndex, firstOriginalIndex,
        (gridPolylineSegments first).get firstOriginalIndex⟩
    let secondIndexed : IndexedGridSegment :=
      ⟨secondRouteIndex, secondOriginalIndex,
        (gridPolylineSegments second).get secondOriginalIndex⟩
    have firstMember :
        firstIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        firstRouteMember firstOriginalIndex
    have secondMember :
        secondIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        secondRouteMember secondOriginalIndex
    have different :
        SegmentOccurrenceKey firstIndexed firstTranslate ≠
          SegmentOccurrenceKey secondIndexed secondTranslate := by
      exact
        segmentOccurrenceKey_ne_of_routeOccurrence_ne
          occurrencesDifferent
    have disjoint :=
      continuous.noInteriorsMeet
        firstMember secondMember different
    simpa [firstIndexed, secondIndexed, firstOffset, secondOffset,
      firstOriginalIndex, secondOriginalIndex,
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
      using disjoint
  · intro firstPointIndex secondSegmentIndex
    let firstOriginalPointIndex : Fin first.length :=
      ⟨firstPointIndex, by simpa using firstPointIndex.isLt⟩
    let secondOriginalSegmentIndex :
        Fin (gridPolylineSegments second).length :=
      ⟨secondSegmentIndex, by
        simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using secondSegmentIndex.isLt⟩
    rcases
        PeriodicOrthocrossing.exists_segment_contains_of_mem
          firstLength firstOrthogonal
          (List.get_mem first firstOriginalPointIndex) with
      ⟨firstSegment, firstSegmentMember, firstContains⟩
    rcases List.mem_iff_get.mp firstSegmentMember with
      ⟨firstOriginalSegmentIndex, firstSegmentEquation⟩
    let firstIndexed : IndexedGridSegment :=
      ⟨firstRouteIndex, firstOriginalSegmentIndex,
        (gridPolylineSegments first).get
          firstOriginalSegmentIndex⟩
    let secondIndexed : IndexedGridSegment :=
      ⟨secondRouteIndex, secondOriginalSegmentIndex,
        (gridPolylineSegments second).get
          secondOriginalSegmentIndex⟩
    have firstMember :
        firstIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        firstRouteMember firstOriginalSegmentIndex
    have secondMember :
        secondIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        secondRouteMember secondOriginalSegmentIndex
    have different :
        SegmentOccurrenceKey secondIndexed secondTranslate ≠
          SegmentOccurrenceKey firstIndexed firstTranslate := by
      exact
        segmentOccurrenceKey_ne_of_routeOccurrence_ne
          (Ne.symm occurrencesDifferent)
    intro secondInterior
    apply
      continuous.isPlanar.1
        secondIndexed secondMember firstIndexed firstMember
        secondTranslate firstTranslate
        (Cell.add firstOffset
          (first.get firstOriginalPointIndex))
        different
    · simpa [secondIndexed, secondOffset,
        secondOriginalSegmentIndex,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
        firstOffset, firstOriginalPointIndex] using
          secondInterior
    · have indexedContains :
          ((gridPolylineSegments first).get
              firstOriginalSegmentIndex).Contains
            (first.get firstOriginalPointIndex) := by
        rw [firstSegmentEquation]
        exact firstContains
      have translatedContains :=
        (contains_translate_iff
          ((gridPolylineSegments first).get
            firstOriginalSegmentIndex)
          firstOffset
          (first.get firstOriginalPointIndex)).2 indexedContains
      simpa [firstIndexed, firstOffset, Cell.add,
        add_comm] using translatedContains
  · intro secondPointIndex firstSegmentIndex
    let secondOriginalPointIndex : Fin second.length :=
      ⟨secondPointIndex, by simpa using secondPointIndex.isLt⟩
    let firstOriginalSegmentIndex :
        Fin (gridPolylineSegments first).length :=
      ⟨firstSegmentIndex, by
        simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using firstSegmentIndex.isLt⟩
    rcases
        PeriodicOrthocrossing.exists_segment_contains_of_mem
          secondLength secondOrthogonal
          (List.get_mem second secondOriginalPointIndex) with
      ⟨secondSegment, secondSegmentMember, secondContains⟩
    rcases List.mem_iff_get.mp secondSegmentMember with
      ⟨secondOriginalSegmentIndex, secondSegmentEquation⟩
    let firstIndexed : IndexedGridSegment :=
      ⟨firstRouteIndex, firstOriginalSegmentIndex,
        (gridPolylineSegments first).get
          firstOriginalSegmentIndex⟩
    let secondIndexed : IndexedGridSegment :=
      ⟨secondRouteIndex, secondOriginalSegmentIndex,
        (gridPolylineSegments second).get
          secondOriginalSegmentIndex⟩
    have firstMember :
        firstIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        firstRouteMember firstOriginalSegmentIndex
    have secondMember :
        secondIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        secondRouteMember secondOriginalSegmentIndex
    have different :
        SegmentOccurrenceKey firstIndexed firstTranslate ≠
          SegmentOccurrenceKey secondIndexed secondTranslate :=
      segmentOccurrenceKey_ne_of_routeOccurrence_ne
        occurrencesDifferent
    intro firstInterior
    apply
      continuous.isPlanar.1
        firstIndexed firstMember secondIndexed secondMember
        firstTranslate secondTranslate
        (Cell.add secondOffset
          (second.get secondOriginalPointIndex))
        different
    · simpa [firstIndexed, firstOffset,
        firstOriginalSegmentIndex,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
        secondOffset, secondOriginalPointIndex] using
          firstInterior
    · have indexedContains :
          ((gridPolylineSegments second).get
              secondOriginalSegmentIndex).Contains
            (second.get secondOriginalPointIndex) := by
        rw [secondSegmentEquation]
        exact secondContains
      have translatedContains :=
        (contains_translate_iff
          ((gridPolylineSegments second).get
            secondOriginalSegmentIndex)
          secondOffset
          (second.get secondOriginalPointIndex)).2 indexedContains
      simpa [secondIndexed, secondOffset, Cell.add,
        add_comm] using translatedContains
  · intro firstPointIndex secondPointIndex pointEqual
    let firstOriginalPointIndex : Fin first.length :=
      ⟨firstPointIndex, by simpa using firstPointIndex.isLt⟩
    let secondOriginalPointIndex : Fin second.length :=
      ⟨secondPointIndex, by simpa using secondPointIndex.isLt⟩
    let firstIndexed : IndexedRoutePoint :=
      { routeIndex := firstRouteIndex
        pointIndex := firstOriginalPointIndex
        routeLength := first.length
        point := first.get firstOriginalPointIndex }
    let secondIndexed : IndexedRoutePoint :=
      { routeIndex := secondRouteIndex
        pointIndex := secondOriginalPointIndex
        routeLength := second.length
        point := second.get secondOriginalPointIndex }
    have firstMember :
        firstIndexed ∈ drawing.indexedRoutePoints :=
      indexedRoutePoint_mem_of_route_mem
        firstRouteMember firstOriginalPointIndex
    have secondMember :
        secondIndexed ∈ drawing.indexedRoutePoints :=
      indexedRoutePoint_mem_of_route_mem
        secondRouteMember secondOriginalPointIndex
    have different :
        RoutePointOccurrenceKey firstIndexed firstTranslate ≠
          RoutePointOccurrenceKey secondIndexed secondTranslate :=
      routePointOccurrenceKey_ne_of_routeOccurrence_ne
        occurrencesDifferent
    have physicalEqual :
        Cell.add firstIndexed.point firstOffset =
          Cell.add secondIndexed.point secondOffset := by
      simpa [firstIndexed, secondIndexed, firstOffset,
        secondOffset, firstOriginalPointIndex,
        secondOriginalPointIndex, Cell.add,
        add_comm] using pointEqual
    have outer :=
      endpointContacts firstIndexed firstMember
        secondIndexed secondMember
        firstTranslate secondTranslate different
        (by simpa [firstOffset, secondOffset] using physicalEqual)
    constructor
    · exact
        routePointIsEndpoint_of_index firstPointIndex
          (by
            simpa [firstIndexed, firstOriginalPointIndex,
              IndexedRoutePoint.IsEndpoint] using outer.1)
    · exact
        routePointIsEndpoint_of_index secondPointIndex
          (by
            simpa [secondIndexed, secondOriginalPointIndex,
              IndexedRoutePoint.IsEndpoint] using outer.2)

end PeriodicGridDrawing
end LeanTrominoes
