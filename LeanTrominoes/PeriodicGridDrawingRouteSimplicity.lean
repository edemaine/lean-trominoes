import LeanTrominoes.PeriodicGridDrawingRibbonSeparation

/-!
# Extracting simple routes from periodic drawing certificates

The global periodic predicates distinguish syntactic point and segment
occurrences, whereas finite ribbon infrastructure uses the route-local
`RouteIsSimple` predicate.  This file bridges those views for one stored
route whose advertised endpoints are distinct.
-/

namespace LeanTrominoes

namespace GridSegment

/-- A segment never contains its own start in its relative interior. -/
theorem not_interiorContains_start (segment : GridSegment) :
    ¬segment.InteriorContains segment.start := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp [InteriorContains, IsHorizontal, IsVertical,
    StrictlyBetween]

/-- A segment never contains its own finish in its relative interior. -/
theorem not_interiorContains_finish (segment : GridSegment) :
    ¬segment.InteriorContains segment.finish := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp [InteriorContains, IsHorizontal, IsVertical,
    StrictlyBetween]

end GridSegment

namespace PeriodicOrthocrossing

/-- Every listed point of a nondegenerate polyline is an endpoint of one
syntactically incident segment. -/
theorem exists_segment_endpoint_of_mem
    {points : List Cell}
    (length : 2 ≤ points.length)
    {point : Cell} (pointMember : point ∈ points) :
    ∃ segment ∈ gridPolylineSegments points,
      point = segment.start ∨ point = segment.finish := by
  induction points using List.twoStepInduction with
  | nil =>
      simp at length
  | singleton only =>
      simp at length
  | cons_cons first second rest _ tailInduction =>
      simp only [List.mem_cons] at pointMember
      rcases pointMember with pointFirst | pointTail
      · subst point
        exact
          ⟨GridSegment.mk first second,
            by simp [gridPolylineSegments], Or.inl rfl⟩
      · cases rest with
        | nil =>
            simp at pointTail
            subst point
            exact
              ⟨GridSegment.mk first second,
                by simp [gridPolylineSegments], Or.inr rfl⟩
        | cons third rest =>
            rcases
                tailInduction second (by simp)
                  (by simpa only [List.mem_cons] using pointTail) with
              ⟨segment, segmentMember, endpoint⟩
            exact
              ⟨segment,
                List.mem_cons_of_mem _ segmentMember,
                endpoint⟩

end PeriodicOrthocrossing

namespace PeriodicGridDrawing

/-- Endpoint-only point contacts make one stored route duplicate-free once
its first and last advertised points are known to differ. -/
theorem route_nodup_of_endpointContacts
    {drawing : PeriodicGridDrawing}
    (endpointContacts :
      drawing.RoutePointsMeetOnlyAtEndpoints)
    {route : List Cell}
    (routeMember : route ∈ drawing.edgeRoutes)
    (length : 2 ≤ route.length)
    {source target : Cell}
    (routeHead : route.head? = some source)
    (routeLast : route.getLast? = some target)
    (endpointsDifferent : source ≠ target) :
    route.Nodup := by
  rcases List.mem_iff_get.mp routeMember with
    ⟨routeIndex, routeEquation⟩
  have indexedRouteMember :
      (route, routeIndex.val) ∈ drawing.edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨routeIndex.isLt, routeEquation⟩
  have getSource
      (index : Fin route.length)
      (indexZero : index.val = 0) :
      route.get index = source := by
    cases route with
    | nil =>
        exact Fin.elim0 index
    | cons head tail =>
        have indexEqual :
            index = ⟨0, by simp⟩ :=
          Fin.ext indexZero
        subst index
        simpa using routeHead
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at length
    simp at length
  have getTarget
      (index : Fin route.length)
      (indexLast : index.val + 1 = route.length) :
      route.get index = target := by
    have lastIndexLt :
        route.length - 1 < route.length := by
      omega
    let lastIndex : Fin route.length :=
      ⟨route.length - 1, lastIndexLt⟩
    have indexEqual : lastIndex = index := by
      apply Fin.ext
      simp [lastIndex]
      omega
    have lastEqual :
        route.getLast routeNonempty = route.get index := by
      rw [← List.get_length_sub_one lastIndexLt]
      exact congrArg (List.get route) indexEqual
    rw [List.getLast?_eq_getLast_of_ne_nil routeNonempty] at routeLast
    exact lastEqual.symm.trans (Option.some.inj routeLast)
  apply List.nodup_iff_injective_get.mpr
  intro firstIndex secondIndex pointEqual
  by_cases indicesEqual : firstIndex = secondIndex
  · exact indicesEqual
  let firstIndexed : IndexedRoutePoint :=
    { routeIndex := routeIndex
      pointIndex := firstIndex
      routeLength := route.length
      point := route.get firstIndex }
  let secondIndexed : IndexedRoutePoint :=
    { routeIndex := routeIndex
      pointIndex := secondIndex
      routeLength := route.length
      point := route.get secondIndex }
  have firstMember :
      firstIndexed ∈ drawing.indexedRoutePoints :=
    indexedRoutePoint_mem_of_route_mem
      indexedRouteMember firstIndex
  have secondMember :
      secondIndexed ∈ drawing.indexedRoutePoints :=
    indexedRoutePoint_mem_of_route_mem
      indexedRouteMember secondIndex
  have keysDifferent :
      RoutePointOccurrenceKey firstIndexed (0, 0) ≠
        RoutePointOccurrenceKey secondIndexed (0, 0) := by
    intro equal
    apply indicesEqual
    apply Fin.ext
    simpa [RoutePointOccurrenceKey,
      firstIndexed, secondIndexed] using
      congrArg (fun key => key.2.1) equal
  have translatedEqual :
      Cell.add firstIndexed.point
          (drawing.periodTranslation (0, 0)) =
        Cell.add secondIndexed.point
          (drawing.periodTranslation (0, 0)) := by
    simpa [firstIndexed, secondIndexed,
      periodTranslation, Cell.scale, Cell.add] using pointEqual
  have endpoints :=
    endpointContacts firstIndexed firstMember
      secondIndexed secondMember
      (0, 0) (0, 0) keysDifferent translatedEqual
  simp only [IndexedRoutePoint.IsEndpoint,
    firstIndexed, secondIndexed] at endpoints
  rcases endpoints with
    ⟨firstZero | firstLast, secondZero | secondLast⟩
  · exact Fin.ext (by omega)
  · exact
      (endpointsDifferent
        ((getSource firstIndex firstZero).symm.trans
          (pointEqual.trans
            (getTarget secondIndex secondLast)))).elim
  · exact
      (endpointsDifferent
        ((getSource secondIndex secondZero).symm.trans
          (pointEqual.symm.trans
            (getTarget firstIndex firstLast)))).elim
  · exact Fin.ext (by omega)

/-- A globally continuously planar, endpoint-contact-certified stored
orthogonal route with distinct advertised endpoints is simple. -/
theorem routeIsSimple_of_globalCertificates
    {drawing : PeriodicGridDrawing}
    (continuous : drawing.IsContinuouslyPlanar)
    (endpointContacts :
      drawing.RoutePointsMeetOnlyAtEndpoints)
    {route : List Cell}
    (routeMember : route ∈ drawing.edgeRoutes)
    (length : 2 ≤ route.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    {source target : Cell}
    (routeHead : route.head? = some source)
    (routeLast : route.getLast? = some target)
    (endpointsDifferent : source ≠ target) :
    LocalIncidenceDrawing.RouteIsSimple route := by
  rcases List.mem_iff_get.mp routeMember with
    ⟨routeIndex, routeEquation⟩
  have indexedRouteMember :
      (route, routeIndex.val) ∈ drawing.edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨routeIndex.isLt, routeEquation⟩
  refine
    ⟨route_nodup_of_endpointContacts endpointContacts
        routeMember length routeHead routeLast endpointsDifferent,
      ?_, ?_⟩
  · intro point pointMember segment segmentMember
    rcases List.mem_iff_get.mp segmentMember with
      ⟨segmentIndex, segmentEquation⟩
    rcases
        PeriodicOrthocrossing.exists_segment_endpoint_of_mem
          length pointMember with
      ⟨incident, incidentMember, pointEndpoint⟩
    rcases List.mem_iff_get.mp incidentMember with
      ⟨incidentIndex, incidentEquation⟩
    intro pointInterior
    by_cases indicesEqual : segmentIndex = incidentIndex
    · have segmentsEqual : segment = incident := by
        calc
          segment =
              (gridPolylineSegments route).get segmentIndex :=
            segmentEquation.symm
          _ =
              (gridPolylineSegments route).get incidentIndex := by
            rw [indicesEqual]
          _ = incident := incidentEquation
      rw [segmentsEqual] at pointInterior
      rcases pointEndpoint with pointStart | pointFinish
      · rw [pointStart] at pointInterior
        exact
          (GridSegment.not_interiorContains_start incident
            pointInterior).elim
      · rw [pointFinish] at pointInterior
        exact
          (GridSegment.not_interiorContains_finish incident
            pointInterior).elim
    · let firstIndexed : IndexedGridSegment :=
        ⟨routeIndex, segmentIndex,
          (gridPolylineSegments route).get segmentIndex⟩
      let secondIndexed : IndexedGridSegment :=
        ⟨routeIndex, incidentIndex,
          (gridPolylineSegments route).get incidentIndex⟩
      have firstMember :
          firstIndexed ∈ drawing.indexedSegments :=
        indexedSegment_mem_of_route_mem
          indexedRouteMember segmentIndex
      have secondMember :
          secondIndexed ∈ drawing.indexedSegments :=
        indexedSegment_mem_of_route_mem
          indexedRouteMember incidentIndex
      have keysDifferent :
          SegmentOccurrenceKey firstIndexed (0, 0) ≠
            SegmentOccurrenceKey secondIndexed (0, 0) := by
        intro equal
        apply indicesEqual
        apply Fin.ext
        simpa [SegmentOccurrenceKey,
          firstIndexed, secondIndexed] using
          congrArg (fun key => key.2.1) equal
      apply
        continuous.isPlanar.1 firstIndexed firstMember
          secondIndexed secondMember
          (0, 0) (0, 0) point keysDifferent
      · have pointInterior' :
            ((gridPolylineSegments route).get
                segmentIndex).InteriorContains point := by
          rw [segmentEquation]
          exact pointInterior
        simpa [firstIndexed, GridSegment.translate,
          periodTranslation, Cell.scale, Cell.add] using
          pointInterior'
      · have incidentContains :
            incident.Contains point := by
          rcases pointEndpoint with pointStart | pointFinish
          · rw [pointStart]
            exact
              GridSegment.contains_start_of_axisAligned
                ((PeriodicOrthocrossing.orthogonalPolyline_iff_segments
                  route).mp orthogonal incident incidentMember)
          · rw [pointFinish]
            exact
              GridSegment.contains_finish_of_axisAligned
                ((PeriodicOrthocrossing.orthogonalPolyline_iff_segments
                  route).mp orthogonal incident incidentMember)
        have incidentContains' :
            ((gridPolylineSegments route).get
                incidentIndex).Contains point := by
          rw [incidentEquation]
          exact incidentContains
        simpa [secondIndexed, GridSegment.translate,
          periodTranslation, Cell.scale, Cell.add] using
          incidentContains'
  · intro first firstMember second secondMember indicesDifferent
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff] at firstMember secondMember
    let firstIndex :
        Fin (gridPolylineSegments route).length :=
      ⟨first.2, firstMember.1⟩
    let secondIndex :
        Fin (gridPolylineSegments route).length :=
      ⟨second.2, secondMember.1⟩
    let firstIndexed : IndexedGridSegment :=
      ⟨routeIndex, firstIndex,
        (gridPolylineSegments route).get firstIndex⟩
    let secondIndexed : IndexedGridSegment :=
      ⟨routeIndex, secondIndex,
        (gridPolylineSegments route).get secondIndex⟩
    have firstGlobalMember :
        firstIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        indexedRouteMember firstIndex
    have secondGlobalMember :
        secondIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        indexedRouteMember secondIndex
    have keysDifferent :
        SegmentOccurrenceKey firstIndexed (0, 0) ≠
          SegmentOccurrenceKey secondIndexed (0, 0) := by
      intro equal
      apply indicesDifferent
      simpa [SegmentOccurrenceKey,
        firstIndexed, secondIndexed,
        firstIndex, secondIndex] using
        congrArg (fun key => key.2.1) equal
    have disjoint :=
      continuous.noInteriorsMeet
        firstGlobalMember secondGlobalMember keysDifferent
    simpa [firstIndexed, secondIndexed,
      firstIndex, secondIndex,
      firstMember.2, secondMember.2,
      GridSegment.translate,
      periodTranslation, Cell.scale, Cell.add] using disjoint

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- Every tagged stored incidence route in a ribbon-ready presentation is
simple in the finite route-local sense. -/
theorem HaloBoundedRibbonReadyIncidencePresentation.routeIsSimple_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      HaloBoundedRibbonReadyIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex) := by
  let planar := presentation.toPlanarIncidencePresentation
  let drawing :=
    incidenceDrawing source placement presentation.routes
  have endpoints :=
    planar.route_endpoints_of_tagged taggedMember
  have routeLength :
      2 ≤
        (presentation.routes
          tagged.1.clauseIndex tagged.1.literalIndex).length := by
    have segmentsNonempty :=
      planar.route_segments_ne_nil_of_tagged taggedMember
    have segmentsPositive :
        0 <
          (gridPolylineSegments
            (presentation.routes
              tagged.1.clauseIndex
              tagged.1.literalIndex)).length :=
      List.length_pos_iff.mpr segmentsNonempty
    rw [gridPolylineSegments_length] at segmentsPositive
    omega
  exact
    PeriodicGridDrawing.routeIsSimple_of_globalCertificates
      presentation.continuouslyPlanar
      presentation.endpointContacts
      (planar.route_mem_of_tagged taggedMember)
      routeLength
      (planar.route_orthogonal_of_tagged taggedMember)
      endpoints.1 endpoints.2
      (planar.route_endpoints_ne_of_tagged taggedMember)

end PositionedPeriodicCNF
end LeanTrominoes
