/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalProximity
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendSeparation
import LeanTrominoes.PeriodicOrthocrossingCrossoverCenterDisjointness
import LeanTrominoes.PeriodicOrthocrossingContinuousParallel
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierCore

/-!
# Selected retained carriers near route bends

This file identifies the two source-segment occurrence terminals adjacent to
an enumerated route bend.  It then classifies a selected carrier whose narrow
lens rectangle overlaps the bend macrocell.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The two endpoint terminals of every segment in a route tail, retaining
the route's segment indices. -/
def routeSegmentTerminalsAux
    (routeIndex : Nat) (translate : Cell) :
    Nat → List Cell → List SegmentTerminal
  | startIndex, first :: second :: rest =>
      [⟨⟨routeIndex, startIndex, ⟨first, second⟩⟩,
          translate, .start⟩,
        ⟨⟨routeIndex, startIndex, ⟨first, second⟩⟩,
          translate, .finish⟩] ++
      routeSegmentTerminalsAux routeIndex translate
        (startIndex + 1) (second :: rest)
  | _, _ => []

/-- The recursive terminal enumeration agrees with flattening the indexed
polyline segments into their two occurrence terminals. -/
theorem routeSegmentTerminalsAux_eq
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat),
      routeSegmentTerminalsAux routeIndex translate startIndex points =
        ((gridPolylineSegments points).zipIdx startIndex).flatMap
          (fun taggedSegment =>
            occurrenceTerminals
              (⟨routeIndex, taggedSegment.2, taggedSegment.1⟩,
                translate)) := by
  intro points
  induction points with
  | nil =>
      intro startIndex
      simp [routeSegmentTerminalsAux, gridPolylineSegments]
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex
          simp [routeSegmentTerminalsAux, gridPolylineSegments]
      | cons second rest =>
          intro startIndex
          simp only [routeSegmentTerminalsAux,
            gridPolylineSegments, List.zipIdx_cons,
            List.flatMap_cons, occurrenceTerminals]
          rw [induction (startIndex + 1)]
          simp only [occurrenceTerminals]

/-- Every terminal of a route tail is either attached to one of its
enumerated bends or is one of the two external endpoints of that tail. -/
theorem routeSegmentTerminal_bend_or_endpoint
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex)
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {terminal : SegmentTerminal},
      terminal ∈
          routeSegmentTerminalsAux
            routeIndex translate startIndex points →
        (∃ routeBend,
            routeBend ∈
                routeBendsAux
                  routeIndex translate startIndex points ∧
              (terminal = routeBend.incomingTerminal ∨
                terminal = routeBend.outgoingTerminal)) ∨
          ∃ endpoint,
            endpoint ∈
                routeEndpointsFromSegments edge routeIndex translate
                  ((gridPolylineSegments points).zipIdx startIndex) ∧
              terminal = endpoint.terminal := by
  intro points
  induction points with
  | nil =>
      intro startIndex terminal terminalMem
      simp [routeSegmentTerminalsAux] at terminalMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex terminal terminalMem
          simp [routeSegmentTerminalsAux] at terminalMem
      | cons second rest =>
          cases rest with
          | nil =>
              intro startIndex terminal terminalMem
              change
                terminal ∈
                  [⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .start⟩,
                    ⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .finish⟩] ++
                    routeSegmentTerminalsAux routeIndex translate
                      (startIndex + 1) [second] at terminalMem
              simp only [routeSegmentTerminalsAux,
                List.append_nil, List.mem_cons,
                List.not_mem_nil, or_false] at terminalMem
              rcases terminalMem with terminalEq | terminalEq <;>
                rw [terminalEq]
              · apply Or.inr
                refine
                  ⟨⟨edge, routeIndex, translate, .source,
                      ⟨⟨routeIndex, startIndex,
                          ⟨first, second⟩⟩,
                        translate, .start⟩⟩, ?_, rfl⟩
                simp [gridPolylineSegments,
                  routeEndpointsFromSegments]
              · apply Or.inr
                refine
                  ⟨⟨edge, routeIndex, translate, .target,
                      ⟨⟨routeIndex, startIndex,
                          ⟨first, second⟩⟩,
                        translate, .finish⟩⟩, ?_, rfl⟩
                simp [gridPolylineSegments,
                  routeEndpointsFromSegments]
          | cons third tail =>
              intro startIndex terminal terminalMem
              change
                terminal ∈
                  [⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .start⟩,
                    ⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .finish⟩] ++
                    routeSegmentTerminalsAux routeIndex translate
                      (startIndex + 1) (second :: third :: tail)
                  at terminalMem
              rw [List.mem_append] at terminalMem
              rcases terminalMem with firstMem | tailMem
              · simp only [List.mem_cons, List.not_mem_nil,
                  or_false] at firstMem
                rcases firstMem with terminalEq | terminalEq
                · rw [terminalEq]
                  apply Or.inr
                  refine
                    ⟨⟨edge, routeIndex, translate, .source,
                        ⟨⟨routeIndex, startIndex,
                            ⟨first, second⟩⟩,
                          translate, .start⟩⟩, ?_, rfl⟩
                  simp [gridPolylineSegments,
                    routeEndpointsFromSegments]
                · rw [terminalEq]
                  apply Or.inl
                  refine
                    ⟨⟨routeIndex, startIndex, translate,
                        first, second, third⟩, ?_, Or.inl rfl⟩
                  simp [routeBendsAux]
              · rcases
                    induction (startIndex + 1) tailMem with
                  tailBend | tailEndpoint
                · rcases tailBend with
                    ⟨routeBend, routeBendMem, terminalEq⟩
                  apply Or.inl
                  refine
                    ⟨routeBend, List.mem_cons_of_mem _ routeBendMem,
                      terminalEq⟩
                · rcases tailEndpoint with
                    ⟨endpoint, endpointMem, terminalEq⟩
                  simp only [gridPolylineSegments,
                    List.zipIdx_cons,
                    routeEndpointsFromSegments,
                    List.mem_cons, List.not_mem_nil,
                    or_false] at endpointMem
                  rcases endpointMem with
                    endpointEq | endpointEq
                  · subst endpoint
                    rw [terminalEq]
                    apply Or.inl
                    refine
                      ⟨⟨routeIndex, startIndex, translate,
                          first, second, third⟩,
                        by simp [routeBendsAux],
                        Or.inr ?_⟩
                    rfl
                  · subst endpoint
                    rw [terminalEq]
                    apply Or.inr
                    refine
                      ⟨⟨edge, routeIndex, translate, .target,
                          ((gridPolylineSegments
                              (first :: second :: third :: tail)).zipIdx
                            startIndex).getLastD
                              (⟨first, second⟩, startIndex)
                            |> fun taggedSegment =>
                              ⟨⟨routeIndex, taggedSegment.2,
                                  taggedSegment.1⟩,
                                translate, .finish⟩⟩,
                        ?_, ?_⟩
                    · simp [gridPolylineSegments,
                        routeEndpointsFromSegments]
                    · simp only [gridPolylineSegments,
                        List.zipIdx_cons, List.getLastD_cons]

/-- Globally, every enumerated segment terminal is either an internal bend
terminal or an external route endpoint. -/
theorem drawingSegmentTerminal_bend_or_routeEndpoint
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph) :
    (∃ routeBend,
        routeBend ∈ drawingRouteBends graph ∧
          (terminal = routeBend.incomingTerminal ∨
            terminal = routeBend.outgoingTerminal)) ∨
      ∃ endpoint,
        endpoint ∈ drawingRouteEndpoints graph ∧
          terminal = endpoint.terminal := by
  rcases List.mem_flatMap.mp terminalMem with
    ⟨occurrence, occurrenceMem, terminalInOccurrence⟩
  have occurrenceData :=
    (mem_neighborOccurrences_iff graph occurrence).mp occurrenceMem
  rcases occurrence with ⟨indexed, translate⟩
  simp only [occurrenceTerminals, List.mem_cons,
    List.not_mem_nil, or_false] at terminalInOccurrence
  rcases terminalInOccurrence with terminalEq | terminalEq
  all_goals
    rcases List.mem_flatMap.mp occurrenceData.1 with
      ⟨taggedRoute, taggedRouteMem, indexedInRoute⟩
    rcases List.mem_map.mp indexedInRoute with
      ⟨taggedSegment, taggedSegmentMem, indexedEq⟩
    have edgeIndexLt :
        taggedRoute.2 < graph.edges.length := by
      have routeIndexLt :=
        List.snd_lt_of_mem_zipIdx taggedRouteMem
      simpa [drawing, constructedEdgeRoutes] using routeIndexLt
    let edge : PeriodicEdge Vertex :=
      graph.edges[taggedRoute.2]'edgeIndexLt
    have edgeMem :
        (edge, taggedRoute.2) ∈ graph.edges.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨edgeIndexLt, rfl⟩
    have constructedRouteMem :=
      constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
        graph edgeMem
    have taggedRouteEq :
        taggedRoute =
          (constructedEdgeRoute graph edge taggedRoute.2,
            taggedRoute.2) :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        taggedRouteMem constructedRouteMem rfl
    have taggedRouteFirstEq :
        taggedRoute.1 =
          constructedEdgeRoute graph edge taggedRoute.2 :=
      congrArg Prod.fst taggedRouteEq
    rw [taggedRouteFirstEq] at taggedSegmentMem
    have indexedEq' :
        (⟨taggedRoute.2, taggedSegment.2,
            taggedSegment.1⟩ : IndexedGridSegment) =
          indexed := by
      simpa using indexedEq
    have localTerminalMem :
        terminal ∈
          routeSegmentTerminalsAux
            taggedRoute.2 translate 0
            (constructedEdgeRoute graph edge taggedRoute.2) := by
      rw [terminalEq, ← indexedEq', routeSegmentTerminalsAux_eq]
      apply List.mem_flatMap.mpr
      refine ⟨taggedSegment, ?_, ?_⟩
      · exact taggedSegmentMem
      · simp [occurrenceTerminals]
    rcases
        routeSegmentTerminal_bend_or_endpoint
          edge taggedRoute.2 translate
          (constructedEdgeRoute graph edge taggedRoute.2) 0
          localTerminalMem with
      localBend | localEndpoint
    · rcases localBend with
        ⟨routeBend, routeBendMem, terminalEq⟩
      apply Or.inl
      refine ⟨routeBend, ?_, terminalEq⟩
      apply List.mem_flatMap.mpr
      refine
        ⟨(constructedEdgeRoute graph edge taggedRoute.2,
            taggedRoute.2),
          ?_, ?_⟩
      · exact constructedRouteMem
      · apply List.mem_flatMap.mpr
        exact
          ⟨translate,
            (mem_neighborTranslations_iff translate).mpr
              occurrenceData.2,
            routeBendMem⟩
    · rcases localEndpoint with
        ⟨endpoint, endpointMem, terminalEq⟩
      apply Or.inr
      refine ⟨endpoint, ?_, terminalEq⟩
      apply List.mem_flatMap.mpr
      refine ⟨(edge, taggedRoute.2), edgeMem, ?_⟩
      · apply List.mem_flatMap.mpr
        exact
          ⟨translate,
            (mem_neighborTranslations_iff translate).mpr
              occurrenceData.2,
            endpointMem⟩

/-- Tagging a nonempty list by successive indices does not change the value
of its last element. -/
theorem zipIdx_getLastD_fst_bendProximity
    {α : Type*} (values : List α) (start : Nat)
    (default : α × Nat) :
    ((values.zipIdx start).getLastD default).1 =
      values.getLastD default.1 := by
  induction values generalizing start with
  | nil => rfl
  | cons first rest induction =>
      cases rest with
      | nil => simp
      | cons second rest =>
          simpa using induction (start := start + 1)

/-- If a point lies in the relative interior of one axis-aligned segment
and is an endpoint of a parallel nondegenerate segment, their continuous
relative interiors overlap. -/
theorem GridSegment.interiorsMeet_of_interiorContains_endpoint
    {first second : GridSegment} {point : Cell}
    (firstContains : first.InteriorContains point)
    (parallel :
      (first.IsHorizontal ∧ second.IsHorizontal) ∨
        (first.IsVertical ∧ second.IsVertical))
    (endpoint :
      point = second.start ∨ point = second.finish) :
    first.InteriorsMeet second := by
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.InteriorContains,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.StrictlyBetween] at firstContains parallel
  simp only [GridSegment.InteriorsMeet,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.OpenIntervalsOverlap,
    GridSegment.StrictlyBetween,
    Prod.mk.injEq] at endpoint ⊢
  rcases parallel with horizontal | vertical
  · apply Or.inl
    refine ⟨horizontal.1, horizontal.2, ?_, ?_⟩
    · rcases firstContains with firstHorizontal | firstVertical
      · rcases endpoint with endpoint | endpoint <;> omega
      · omega
    · rcases firstContains with firstHorizontal | firstVertical
      · rcases endpoint with endpoint | endpoint <;>
          rcases firstHorizontal.2.2 with between | between <;>
            simp only [min_def, max_def] <;> split_ifs <;> omega
      · omega
  · apply Or.inr
    apply Or.inl
    refine ⟨vertical.1, vertical.2, ?_, ?_⟩
    · rcases firstContains with firstHorizontal | firstVertical
      · omega
      · rcases endpoint with endpoint | endpoint <;> omega
    · rcases firstContains with firstHorizontal | firstVertical
      · omega
      · rcases endpoint with endpoint | endpoint <;>
          rcases firstVertical.2.2 with between | between <;>
            simp only [min_def, max_def] <;> split_ifs <;> omega

/-- Every semantic inner point of a constructed route has a vertical
segment on at least one side. -/
theorem routeBendCenterPlacements_map_hasVertical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat) :
    (routeBendCenterPlacements graph edge edgeIndex).map
        (fun _ => true) =
      let vertical :=
        (classifiedRouteSegments graph edge edgeIndex).map
          (fun classified => classified.role.isVerticalRole)
      List.zipWith (· || ·) vertical vertical.tail := by
  simp [routeBendCenterPlacements,
    classifiedRouteSegments, classifiedSourceFanout,
    classifiedEdgeCore, classifiedTargetFanout,
    SegmentRole.isVerticalRole]
  all_goals split <;> simp_all
  all_goals try split <;> simp_all
  all_goals try split <;> simp_all
  all_goals
    by_cases targetSame :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex) <;>
      simp_all

/-- The two classified segments adjacent to a semantic inner route point
cannot both be horizontal. -/
theorem routeBendCenterPlacement_adjacent_vertical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    (edgeIndex : Nat)
    {placement : RouteBendCenterPlacement Vertex × Nat}
    (placementMem :
      placement ∈
        (routeBendCenterPlacements
          graph edge edgeIndex).zipIdx)
    {incoming outgoing : ClassifiedSegment Vertex × Nat}
    (incomingMem :
      incoming ∈
        (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (outgoingMem :
      outgoing ∈
        (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (incomingIndex : incoming.2 = placement.2)
    (outgoingIndex : outgoing.2 = placement.2 + 1)
    (incomingAligned : incoming.1.segment.IsAxisAligned)
    (outgoingAligned : outgoing.1.segment.IsAxisAligned) :
    incoming.1.segment.IsVertical ∨
      outgoing.1.segment.IsVertical := by
  let vertical :=
    (classifiedRouteSegments graph edge edgeIndex).map
      (fun classified => classified.role.isVerticalRole)
  have placementFlagMem :
      (true, placement.2) ∈
        ((routeBendCenterPlacements
          graph edge edgeIndex).map (fun _ => true)).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨placement, placementMem, rfl⟩
  have placementFlagAt :=
    (List.mem_zipIdx_iff_getElem?).mp placementFlagMem
  have incomingFlagMem :
      (incoming.1.role.isVerticalRole, incoming.2) ∈
        vertical.zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨incoming, incomingMem, rfl⟩
  have outgoingFlagMem :
      (outgoing.1.role.isVerticalRole, outgoing.2) ∈
        vertical.zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨outgoing, outgoingMem, rfl⟩
  have incomingFlagAtRaw :=
    (List.mem_zipIdx_iff_getElem?).mp incomingFlagMem
  have outgoingFlagAtRaw :=
    (List.mem_zipIdx_iff_getElem?).mp outgoingFlagMem
  have incomingFlagAt :
      vertical[placement.2]? =
        some incoming.1.role.isVerticalRole := by
    rw [← incomingIndex, incomingFlagAtRaw]
  have outgoingFlagAt :
      vertical[placement.2 + 1]? =
        some outgoing.1.role.isVerticalRole := by
    rw [← outgoingIndex, outgoingFlagAtRaw]
  have outgoingTailFlagAt :
      vertical.tail[placement.2]? =
        some outgoing.1.role.isVerticalRole := by
    simpa only [List.getElem?_tail] using outgoingFlagAt
  have adjacentFlagAt :
      (List.zipWith (· || ·) vertical vertical.tail)[placement.2]? =
        some
          (incoming.1.role.isVerticalRole ||
            outgoing.1.role.isVerticalRole) := by
    simp [List.getElem?_zipWith,
      incomingFlagAt, outgoingTailFlagAt]
  rw [routeBendCenterPlacements_map_hasVertical
    graph edge edgeIndex] at placementFlagAt
  rw [adjacentFlagAt] at placementFlagAt
  have oneVertical :
      incoming.1.role.isVerticalRole = true ∨
        outgoing.1.role.isVerticalRole = true := by
    have orEqual :
        (incoming.1.role.isVerticalRole ||
          outgoing.1.role.isVerticalRole) = true :=
      (Option.some.inj placementFlagAt.symm).symm
    by_cases incomingVertical :
        incoming.1.role.isVerticalRole = true
    · exact Or.inl incomingVertical
    · apply Or.inr
      cases outgoingVertical :
          outgoing.1.role.isVerticalRole <;>
        simp_all
  rcases oneVertical with incomingVertical | outgoingVertical
  · apply Or.inl
    exact incomingAligned.resolve_left fun incomingHorizontal =>
      have incomingHorizontalRole :=
        classifiedSegment_horizontalRole_of_isHorizontal
          (List.fst_mem_of_mem_zipIdx incomingMem)
          incomingHorizontal
      by
        cases roleEq : incoming.1.role <;>
          simp_all [SegmentRole.isVerticalRole,
            SegmentRole.IsHorizontalRole]
  · apply Or.inr
    exact outgoingAligned.resolve_left fun outgoingHorizontal =>
      have outgoingHorizontalRole :=
        classifiedSegment_horizontalRole_of_isHorizontal
          (List.fst_mem_of_mem_zipIdx outgoingMem)
          outgoingHorizontal
      by
        cases roleEq : outgoing.1.role <;>
          simp_all [SegmentRole.isVerticalRole,
            SegmentRole.IsHorizontalRole]

/-- No interior point of a translated horizontal classified segment lies
on the periodically repeated height-three port row. -/
theorem horizontalClassified_interior_point_snd_ne_portRow
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈
        classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.segment.IsHorizontal)
    (translate point : Cell)
    (contains :
      (classified.segment.translate
        ((drawing graph).periodTranslation translate)).InteriorContains
          point)
    (portTranslate : Int) :
    point.2 ≠
      3 + (drawing graph).gridSize * portTranslate := by
  intro pointYBase
  have horizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      classifiedMem horizontal
  have translatedHorizontal :
      (classified.segment.translate
        ((drawing graph).periodTranslation translate)).IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mpr horizontal
  have pointY :
      point.2 =
        classified.segment.start.2 +
          drawingGridSize graph * translate.2 := by
    rcases contains with
      ⟨_horizontal, sameY, _between⟩ |
        ⟨vertical, _sameX, _between⟩
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        drawing_gridSize, Cell.add, Cell.scale,
        add_comm] using sameY
    · exact (translatedHorizontal.2 vertical.1).elim
  have lane :=
    classifiedSegment_horizontal_lane
      classifiedMem horizontalRole
  have laneBounds :=
    horizontalLaneBase_bounds
      edgeMem classifiedMem horizontalRole
  have threeBounds :
      0 ≤ (3 : Int) ∧
        (3 : Int) < (drawing graph).gridSize := by
    rw [drawing_gridSize]
    have sizePositive := drawingGridSize_pos graph
    unfold drawingGridSize at sizePositive ⊢
    omega
  have laneBounds' :
      0 ≤ horizontalLaneBase classified.role ∧
        horizontalLaneBase classified.role <
          (drawing graph).gridSize := by
    simpa [drawing_gridSize] using laneBounds
  have lanePeriodicEqual :
      (3 : Int) + (drawing graph).gridSize * portTranslate =
        horizontalLaneBase classified.role +
          (drawing graph).gridSize *
            (horizontalLaneCellShift edge classified.role +
              translate.2) := by
    rw [drawing_gridSize]
    rw [lane] at pointY
    rw [pointYBase] at pointY
    simpa [mul_add, add_assoc] using pointY
  have laneBaseEqual :=
    ((drawing graph).translatedHalfOpenCoordinates_eq
      threeBounds laneBounds' lanePeriodicEqual).1
  cases roleEq : classified.role <;>
    simp_all [SegmentRole.IsHorizontalRole,
      horizontalLaneBase, edgeTrack] <;>
    omega

/-- The same port-row exclusion for an arbitrary indexed drawing-segment
occurrence. -/
theorem drawing_horizontal_interior_point_snd_ne_portRow
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (translate point : Cell)
    (horizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).IsHorizontal)
    (contains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).InteriorContains
          point)
    (portTranslate : Int) :
    point.2 ≠
      3 + (drawing graph).gridSize * portTranslate := by
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨taggedRoute, taggedRouteMem,
      taggedClassified, taggedClassifiedMem, indexedEq⟩
  subst indexed
  have edgeMem :
      taggedRoute.1 ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx taggedRouteMem
  have storedHorizontal :
      taggedClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp horizontal
  exact
    horizontalClassified_interior_point_snd_ne_portRow
      edgeMem
      (List.fst_mem_of_mem_zipIdx taggedClassifiedMem)
      storedHorizontal translate point contains portTranslate

/-- The final segment of a nonempty polyline-segment list finishes at the
last point of the polyline. -/
theorem gridPolylineSegments_getLastD_finish_bendProximity
    (points : List Cell)
    (segmentsNonempty :
      gridPolylineSegments points ≠ [])
    (segmentDefault : GridSegment)
    (pointDefault : Cell) :
    ((gridPolylineSegments points).getLastD
      segmentDefault).finish =
      points.getLastD pointDefault := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [gridPolylineSegments] at segmentsNonempty
  | singleton point =>
      simp [gridPolylineSegments] at segmentsNonempty
  | cons_cons first second rest _ induction =>
      cases rest with
      | nil =>
          simp [gridPolylineSegments]
      | cons third rest =>
          have tailNonempty :
              gridPolylineSegments
                (second :: third :: rest) ≠ [] := by
            simp [gridPolylineSegments]
          simpa [gridPolylineSegments] using
            induction second tailNonempty

/-- Every enumerated external route terminal is located at its lifted graph
vertex occurrence. -/
theorem drawingRouteEndpoint_terminal_drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    {endpoint : RouteEndpoint Vertex}
    (endpointMem : endpoint ∈ drawingRouteEndpoints graph) :
    endpoint.terminal.drawingPoint graph =
      Cell.add
        ((drawing graph).vertexPosition graph
          endpoint.vertexOccurrence.1)
        ((drawing graph).periodTranslation
          endpoint.vertexOccurrence.2) := by
  rcases List.mem_flatMap.mp endpointMem with
    ⟨taggedEdge, taggedEdgeMem, translatedEndpointsMem⟩
  rcases List.mem_flatMap.mp translatedEndpointsMem with
    ⟨translate, _translateMem, localEndpointMem⟩
  have endpointVertices :=
    wellFormed.2 taggedEdge.1
      (List.fst_mem_of_mem_zipIdx taggedEdgeMem)
  let route :=
    constructedEdgeRoute graph taggedEdge.1 taggedEdge.2
  have routeHead :
      route.head? =
        some
          (vertexPosition
            (graph.vertices.idxOf taggedEdge.1.source)) := by
    exact constructedEdgeRoute_head?
      graph taggedEdge.1 taggedEdge.2
  have routeLast :
      route.getLast? =
        some
          (Cell.add
            (vertexPosition
              (graph.vertices.idxOf taggedEdge.1.target))
            (Cell.scale (drawingGridSize graph : Int)
              taggedEdge.1.offset)) := by
    exact constructedEdgeRoute_getLast?
      graph taggedEdge.1 taggedEdge.2
  have routeLong : 2 ≤ route.length := by
    dsimp [route]
    unfold constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf taggedEdge.1.source))
        (portX graph
          (sourcePort taggedEdge.1 taggedEdge.2))
    omega
  have segmentsNonempty :
      gridPolylineSegments route ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    rw [gridPolylineSegments_length] at lengthZero
    simp only [List.length_nil] at lengthZero
    omega
  unfold translatedEdgeRouteEndpoints at localEndpointMem
  change
    endpoint ∈
      routeEndpointsFromSegments
        taggedEdge.1 taggedEdge.2 translate
          ((gridPolylineSegments route).zipIdx)
      at localEndpointMem
  generalize segmentsEq :
      (gridPolylineSegments route).zipIdx = segments
  cases segments with
  | nil =>
      have lengthEq := congrArg List.length segmentsEq
      have lengthZero :
          (gridPolylineSegments route).length = 0 := by
        simpa using lengthEq
      have untaggedEmpty :
          gridPolylineSegments route = [] :=
        List.length_eq_zero_iff.mp lengthZero
      exact (segmentsNonempty untaggedEmpty).elim
  | cons firstSegment rest =>
      rw [segmentsEq] at localEndpointMem
      simp only [routeEndpointsFromSegments,
        List.mem_cons, List.not_mem_nil,
        or_false] at localEndpointMem
      rcases localEndpointMem with
        endpointEq | endpointEq <;> subst endpoint
      · have routePoints :
          ∃ first second rest,
            route = first :: second :: rest := by
          cases routeEq : route with
          | nil =>
              rw [routeEq] at routeLong
              simp at routeLong
          | cons first rest =>
              cases restEq : rest with
              | nil =>
                  rw [routeEq, restEq] at routeLong
                  simp at routeLong
              | cons second rest =>
                  exact ⟨first, second, rest, by simp_all⟩
        rcases routePoints with
          ⟨first, second, rest, routeEq⟩
        have firstSegmentEq :
            firstSegment =
              (⟨first, second⟩, 0) := by
          rw [routeEq] at segmentsEq
          simp [gridPolylineSegments] at segmentsEq
          exact segmentsEq.1.symm
        rw [firstSegmentEq]
        have headEq :
            first =
              vertexPosition
                (graph.vertices.idxOf taggedEdge.1.source) := by
          rw [routeEq] at routeHead
          simpa using Option.some.inj routeHead
        simp only [RouteEndpoint.vertexOccurrence]
        rw [drawing_vertexPosition_of_mem
          graph endpointVertices.1]
        simp [SegmentTerminal.drawingPoint,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale,
          headEq]
        constructor <;> ring
      · have lastSegmentFinish :
          (((gridPolylineSegments route).zipIdx).getLastD
              firstSegment).1.finish =
            route.getLastD (0, 0) := by
          rw [zipIdx_getLastD_fst_bendProximity]
          exact
            gridPolylineSegments_getLastD_finish_bendProximity
              route segmentsNonempty firstSegment.1 (0, 0)
        rw [segmentsEq] at lastSegmentFinish
        have routeLastD :
            route.getLastD (0, 0) =
              Cell.add
                (vertexPosition
                  (graph.vertices.idxOf taggedEdge.1.target))
                (Cell.scale (drawingGridSize graph : Int)
                  taggedEdge.1.offset) := by
          rw [List.getLastD_eq_getLast?, routeLast]
          rfl
        have finishEq :=
          lastSegmentFinish.trans routeLastD
        simp only [RouteEndpoint.vertexOccurrence]
        rw [drawing_vertexPosition_of_mem
          graph endpointVertices.2]
        simp [SegmentTerminal.drawingPoint,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale] at finishEq ⊢
        rw [finishEq]
        constructor <;> ring

/-- The lifted vertex named by an enumerated external route endpoint is a
declared graph vertex. -/
theorem drawingRouteEndpoint_vertex_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    {endpoint : RouteEndpoint Vertex}
    (endpointMem : endpoint ∈ drawingRouteEndpoints graph) :
    endpoint.vertexOccurrence.1 ∈ graph.vertices := by
  rcases List.mem_flatMap.mp endpointMem with
    ⟨taggedEdge, taggedEdgeMem, translatedEndpointsMem⟩
  rcases List.mem_flatMap.mp translatedEndpointsMem with
    ⟨translate, _translateMem, localEndpointMem⟩
  have endpointVertices :=
    wellFormed.2 taggedEdge.1
      (List.fst_mem_of_mem_zipIdx taggedEdgeMem)
  unfold translatedEdgeRouteEndpoints at localEndpointMem
  generalize segmentsEq :
      (gridPolylineSegments
        (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2)).zipIdx =
          segments at localEndpointMem
  cases segments with
  | nil =>
      simp [routeEndpointsFromSegments] at localEndpointMem
  | cons first rest =>
      simp only [routeEndpointsFromSegments, List.mem_cons,
        List.not_mem_nil, or_false] at localEndpointMem
      rcases localEndpointMem with endpointEq | endpointEq <;>
        subst endpoint
      · simpa [RouteEndpoint.vertexOccurrence] using endpointVertices.1
      · simpa [RouteEndpoint.vertexOccurrence] using endpointVertices.2

/-- Both segment terminals adjacent to an enumerated bend belong to the
neighboring terminal enumeration used by retained carrier chains. -/
theorem drawingRouteBend_terminals_mem_drawingSegmentTerminals
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup) :
    routeBend.incomingTerminal ∈ drawingSegmentTerminals graph ∧
      routeBend.outgoingTerminal ∈ drawingSegmentTerminals graph := by
  have rawMem :
      routeBend ∈ drawingRouteBends graph :=
    List.mem_dedup.mp routeBendMem
  rcases List.mem_flatMap.mp rawMem with
    ⟨taggedRoute, taggedRouteMem, translatedBendsMem⟩
  rcases List.mem_flatMap.mp translatedBendsMem with
    ⟨translate, translateMem, localBendMem⟩
  have incomingSegmentMem :=
    routeBendsAux_member_incomingSegment_zipIdx
      taggedRoute.2 translate taggedRoute.1 0 localBendMem
  have outgoingSegmentMem :=
    routeBendsAux_member_outgoingSegment_zipIdx
      taggedRoute.2 translate taggedRoute.1 0 localBendMem
  have bendData :=
    routeBendsAux_member_data
      taggedRoute.2 translate taggedRoute.1 0 localBendMem
  have incomingIndexedMem :
      routeBend.incomingTerminal.indexed ∈
        (drawing graph).indexedSegments := by
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine ⟨taggedRoute, taggedRouteMem, ?_⟩
    apply List.mem_map.mpr
    refine
      ⟨(⟨routeBend.incomingStart, routeBend.bend⟩,
          routeBend.incomingSegmentIndex),
        incomingSegmentMem, ?_⟩
    simp [RouteBend.incomingTerminal, bendData.1]
  have outgoingIndexedMem :
      routeBend.outgoingTerminal.indexed ∈
        (drawing graph).indexedSegments := by
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine ⟨taggedRoute, taggedRouteMem, ?_⟩
    apply List.mem_map.mpr
    refine
      ⟨(⟨routeBend.bend, routeBend.outgoingFinish⟩,
          routeBend.incomingSegmentIndex + 1),
        outgoingSegmentMem, ?_⟩
    simp [RouteBend.outgoingTerminal, bendData.1]
  have translateNeighbor :
      IsNeighborTranslation routeBend.translate := by
    rw [bendData.2.1]
    exact (mem_neighborTranslations_iff translate).mp translateMem
  constructor
  · exact
      mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
        graph routeBend.incomingTerminal incomingIndexedMem
        translateNeighbor
  · exact
      mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
        graph routeBend.outgoingTerminal outgoingIndexedMem
        translateNeighbor

/-- Every enumerated bend has a vertical adjacent segment.  This is a
construction-specific fact: horizontal track pieces are always separated
by a port, gate, or boundary column. -/
theorem drawingRouteBend_incomingVertical_or_outgoingVertical
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    (GridSegment.mk
        routeBend.incomingStart routeBend.bend).IsVertical ∨
      (GridSegment.mk
        routeBend.bend routeBend.outgoingFinish).IsVertical := by
  rcases drawingRouteBend_adjacentClassifiedSegments
      graph routeBendMem with
    ⟨edge, edgeIndex, incoming, outgoing,
      edgeMem, incomingMem, outgoingMem,
      routeIndexEq, incomingIndexEq, outgoingIndexEq,
      incomingSegmentEq, outgoingSegmentEq⟩
  rcases drawingRouteBend_centerPlacement
      graph isLocal routeBendMem with
    ⟨placementEdge, placementEdgeIndex,
      placement, placementIndex,
      placementEdgeMem, placementMem,
      placementRouteIndexEq, placementIndexEq,
      _placementPointEq⟩
  have edgeIndexEq :
      placementEdgeIndex = edgeIndex := by
    rw [← placementRouteIndexEq, ← routeIndexEq]
  have taggedEdgeEq :
      (placementEdge, placementEdgeIndex) =
        (edge, edgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      placementEdgeMem edgeMem edgeIndexEq
  have placementEdgeEq :
      placementEdge = edge :=
    congrArg Prod.fst taggedEdgeEq
  subst placementEdge
  rw [edgeIndexEq] at placementMem
  have incomingPlacementIndexEq :
      incoming.2 = placementIndex := by
    omega
  have outgoingPlacementIndexEq :
      outgoing.2 = placementIndex + 1 := by
    omega
  have geometry :=
    drawingRouteBend_cornerGeometry
      wellFormed degree isLocal routeBendMem
  have incomingAligned :
      incoming.1.segment.IsAxisAligned := by
    rw [incomingSegmentEq]
    exact geometry.incomingAligned
  have outgoingAligned :
      outgoing.1.segment.IsAxisAligned := by
    rw [outgoingSegmentEq]
    exact geometry.outgoingAligned
  rcases
      routeBendCenterPlacement_adjacent_vertical
        graph edge edgeIndex placementMem
        incomingMem outgoingMem
        incomingPlacementIndexEq outgoingPlacementIndexEq
        incomingAligned outgoingAligned with
    incomingVertical | outgoingVertical
  · apply Or.inl
    rw [← incomingSegmentEq]
    exact incomingVertical
  · apply Or.inr
    rw [← outgoingSegmentEq]
    exact outgoingVertical

/-- If both segments adjacent to a bend are vertical, its center lies on a
periodic copy of the reserved height-three port row. -/
theorem drawingRouteBend_drawingPoint_snd_eq_portRow_of_adjacent_vertical
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph)
    (incomingVertical :
      (GridSegment.mk
        routeBend.incomingStart routeBend.bend).IsVertical)
    (outgoingVertical :
      (GridSegment.mk
        routeBend.bend routeBend.outgoingFinish).IsVertical) :
    ∃ translateY : Int,
      (routeBend.drawingPoint graph).2 =
        3 + (drawing graph).gridSize * translateY := by
  rcases drawingRouteBend_adjacentClassifiedSegments
      graph routeBendMem with
    ⟨edge, edgeIndex, incoming, outgoing,
      edgeMem, incomingMem, outgoingMem,
      routeIndexEq, incomingIndexEq, outgoingIndexEq,
      incomingSegmentEq, outgoingSegmentEq⟩
  have incomingVertical' :
      incoming.1.segment.IsVertical := by
    rw [incomingSegmentEq]
    exact incomingVertical
  have outgoingVertical' :
      outgoing.1.segment.IsVertical := by
    rw [outgoingSegmentEq]
    exact outgoingVertical
  rcases drawingRouteBend_centerPlacement
      graph isLocal routeBendMem with
    ⟨placementEdge, placementEdgeIndex,
      placement, placementIndex,
      placementEdgeMem, placementMem,
      placementRouteIndexEq, placementIndexEq,
      placementPointEq⟩
  have edgeIndexEq :
      placementEdgeIndex = edgeIndex := by
    rw [← placementRouteIndexEq, ← routeIndexEq]
  have taggedEdgeEq :
      (placementEdge, placementEdgeIndex) =
        (edge, edgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      placementEdgeMem edgeMem edgeIndexEq
  have placementEdgeEq :
      placementEdge = edge :=
    congrArg Prod.fst taggedEdgeEq
  subst placementEdge
  rw [edgeIndexEq] at placementMem
  have incomingPlacementIndexEq :
      incoming.2 = placementIndex := by
    omega
  have outgoingPlacementIndexEq :
      outgoing.2 = placementIndex + 1 := by
    omega
  rcases
      routeBendCenterPlacement_kind_port_of_adjacent_vertical
        graph edge edgeIndex placementMem
        incomingMem outgoingMem
        incomingPlacementIndexEq outgoingPlacementIndexEq
        incomingVertical' outgoingVertical' with
    ⟨port, placementKindEq⟩
  refine
    ⟨(Cell.add routeBend.translate placement.offset).2, ?_⟩
  have pointYEq := congrArg Prod.snd placementPointEq
  rw [placementKindEq] at pointYEq
  simpa [RouteBendCenterKind.position,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale] using pointYEq

/-- If the interior of one retained source occurrence contains the endpoint
of a parallel neighboring segment occurrence, continuous lane uniqueness
identifies the two occurrence keys. -/
theorem retainedCarrierNode_carrierKey_eq_terminal_of_parallel_endpoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    (nodeContains :
      (node.supportingSegment graph).InteriorContains
        (terminal.drawingPoint graph))
    (parallel :
      ((node.supportingSegment graph).IsHorizontal ∧
          ((CarrierNode.terminal terminal).supportingSegment
            graph).IsHorizontal) ∨
        ((node.supportingSegment graph).IsVertical ∧
          ((CarrierNode.terminal terminal).supportingSegment
            graph).IsVertical)) :
    node.carrierKey = terminal.carrierKey := by
  have terminalEndpoint :
      terminal.drawingPoint graph =
          ((CarrierNode.terminal terminal).supportingSegment graph).start ∨
        terminal.drawingPoint graph =
          ((CarrierNode.terminal terminal).supportingSegment graph).finish := by
    rcases terminal with ⟨indexed, translate, endpoint⟩
    cases endpoint <;>
      simp [SegmentTerminal.drawingPoint,
        CarrierNode.supportingSegment, CarrierNode.indexed,
        CarrierNode.translate]
  have interiorsMeet :
      (node.supportingSegment graph).InteriorsMeet
        ((CarrierNode.terminal terminal).supportingSegment graph) :=
    GridSegment.interiorsMeet_of_interiorContains_endpoint
      nodeContains parallel terminalEndpoint
  have nodeIndexedMem :
      node.indexed ∈ (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph nodeMem
  have terminalIndexedMem :
      terminal.indexed ∈ (drawing graph).indexedSegments :=
    (drawingSegmentTerminal_indexed_mem graph terminalMem).1
  rcases parallel with horizontal | vertical
  · have keyEq :=
      drawing_hasUniqueHorizontalContinuousInteriors
        wellFormed degree isLocal
        node.indexed nodeIndexedMem
        terminal.indexed terminalIndexedMem
        node.translate terminal.translate
        horizontal.1 horizontal.2 interiorsMeet
    simpa [CarrierNode.carrierKey_eq_indexed_translate,
      SegmentTerminal.carrierKey] using keyEq
  · have keyEq :=
      drawing_hasUniqueVerticalContinuousInteriors
        wellFormed degree isLocal
        node.indexed nodeIndexedMem
        terminal.indexed terminalIndexedMem
        node.translate terminal.translate
        vertical.1 vertical.2 interiorsMeet
    simpa [CarrierNode.carrierKey_eq_indexed_translate,
      SegmentTerminal.carrierKey] using keyEq

/-- A neighboring segment terminal at an enumerated bend center must be one
of that bend's two adjacent terminals.  External route endpoints cannot occur
there because bend centers are disjoint from lifted graph vertices. -/
theorem drawingSegmentTerminal_eq_routeBend_terminal_of_drawingPoint_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup)
    (pointEq :
      terminal.drawingPoint graph =
        routeBend.drawingPoint graph) :
    terminal = routeBend.incomingTerminal ∨
      terminal = routeBend.outgoingTerminal := by
  rcases
      drawingSegmentTerminal_bend_or_routeEndpoint
        graph terminalMem with
    terminalBend | terminalEndpoint
  · rcases terminalBend with
      ⟨otherBend, otherBendMem, terminalEq⟩
    have otherPointEq :
        terminal.drawingPoint graph =
          otherBend.drawingPoint graph := by
      rcases terminalEq with terminalEq | terminalEq
      · simp [terminalEq]
      · simp [terminalEq]
    have bendEq :=
      drawingRouteBends_eq_of_drawingPoint_eq
        graph wellFormed degree isLocal
        otherBendMem (List.mem_dedup.mp routeBendMem)
        (otherPointEq.symm.trans pointEq)
    subst otherBend
    exact terminalEq
  · rcases terminalEndpoint with
      ⟨endpoint, endpointMem, terminalEq⟩
    have endpointPoint :=
      drawingRouteEndpoint_terminal_drawingPoint
        wellFormed endpointMem
    have endpointVertexMem :=
      drawingRouteEndpoint_vertex_mem
        wellFormed endpointMem
    have endpointAtBend :
        routeBend.drawingPoint graph =
          Cell.add
            ((drawing graph).vertexPosition graph
              endpoint.vertexOccurrence.1)
            ((drawing graph).periodTranslation
              endpoint.vertexOccurrence.2) := by
      rw [← pointEq, terminalEq]
      exact endpointPoint
    exact
      ((drawingRouteBend_drawingPoint_ne_liftedVertexPosition
          wellFormed degree isLocal endpointVertexMem
          endpoint.vertexOccurrence.2
          (List.mem_dedup.mp routeBendMem))
        endpointAtBend).elim

/-- If a raw retained carrier lens whose source translate lies in the
neighbor window overlaps a bend macrocell, the lens is incident to one of
that bend's two terminals. -/
theorem
    retainedDrawingCompleteCarrierLinkRaw_incidentToRouteBend_of_macrocell_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (firstTranslateNeighbor :
      IsNeighborTranslation link.first.translate)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower
          (routeBend.drawingPoint graph))
        (planarSATMacrocellRouteUpper
          (routeBend.drawingPoint graph))) :
    CarrierLinkIncidentToRouteBend link routeBend := by
  have linkEndpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have firstIndexedMem :
      link.first.indexed ∈ (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph linkEndpoints.1
  have bendTerminalMem :=
    drawingRouteBend_terminals_mem_drawingSegmentTerminals
      graph routeBendMem
  have incidentOfTerminal :
      ∀ terminal : SegmentTerminal,
        terminal ∈ drawingSegmentTerminals graph →
        terminal.drawingPoint graph =
          routeBend.drawingPoint graph →
        link.first.carrierKey = terminal.carrierKey →
        CarrierLinkIncidentToRouteBend link routeBend := by
    intro terminal terminalMem terminalPointEq keyEq
    have linkTerminal :=
      retainedDrawingCompleteCarrierLinkRaw_incidentToTerminal_of_key_eq_of_overlap
        wellFormed degree isLocal linkMem terminalMem keyEq
        (by simpa [terminalPointEq] using notSeparated)
    have bendTerminal :=
      drawingSegmentTerminal_eq_routeBend_terminal_of_drawingPoint_eq
        wellFormed degree isLocal terminalMem routeBendMem
        terminalPointEq
    rcases bendTerminal with terminalEq | terminalEq
    · subst terminal
      rcases linkTerminal with firstEq | secondEq
      · exact Or.inl firstEq
      · exact Or.inr (Or.inr (Or.inl secondEq))
    · subst terminal
      rcases linkTerminal with firstEq | secondEq
      · exact Or.inr (Or.inl firstEq)
      · exact Or.inr (Or.inr (Or.inr secondEq))
  have centerContains :=
    retainedDrawingCompleteCarrierLinkRaw_supportingSegment_contains_of_macrocell_overlap
      wellFormed degree isLocal linkMem
      (routeBend.drawingPoint graph) notSeparated
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        centerContains with
    centerInterior | centerEndpoint
  · have firstAligned :
        link.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        link.first.indexed firstIndexedMem
    have supportAligned :
        (link.first.supportingSegment graph).IsAxisAligned := by
      rcases firstAligned with firstHorizontal | firstVertical
      · exact Or.inl
          ((GridSegment.isHorizontal_translate _ _).mpr
            firstHorizontal)
      · exact Or.inr
          ((GridSegment.isVertical_translate _ _).mpr
            firstVertical)
    have geometry :=
      drawingRouteBendDedup_cornerGeometry
        wellFormed degree isLocal routeBendMem
    rcases supportAligned with
      supportHorizontal | supportVertical
    · rcases geometry.incomingAligned with
        incomingHorizontal | incomingVertical
      · have terminalSupportHorizontal :
            ((CarrierNode.terminal
              routeBend.incomingTerminal).supportingSegment
                graph).IsHorizontal := by
          simpa [CarrierNode.supportingSegment,
            CarrierNode.indexed, CarrierNode.translate,
            RouteBend.incomingTerminal] using
            (GridSegment.isHorizontal_translate
              (GridSegment.mk
                routeBend.incomingStart routeBend.bend)
              ((drawing graph).periodTranslation
                routeBend.translate)).mpr incomingHorizontal
        have keyEq :=
          retainedCarrierNode_carrierKey_eq_terminal_of_parallel_endpoint
            wellFormed degree isLocal linkEndpoints.1
            bendTerminalMem.1
            (by simpa using centerInterior)
            (Or.inl ⟨supportHorizontal,
              terminalSupportHorizontal⟩)
        exact incidentOfTerminal routeBend.incomingTerminal
          bendTerminalMem.1 (by simp) keyEq
      · rcases geometry.outgoingAligned with
          outgoingHorizontal | outgoingVertical
        · have terminalSupportHorizontal :
              ((CarrierNode.terminal
                routeBend.outgoingTerminal).supportingSegment
                  graph).IsHorizontal := by
            simpa [CarrierNode.supportingSegment,
              CarrierNode.indexed, CarrierNode.translate,
              RouteBend.outgoingTerminal] using
              (GridSegment.isHorizontal_translate
                (GridSegment.mk
                  routeBend.bend routeBend.outgoingFinish)
                ((drawing graph).periodTranslation
                  routeBend.translate)).mpr outgoingHorizontal
          have keyEq :=
            retainedCarrierNode_carrierKey_eq_terminal_of_parallel_endpoint
              wellFormed degree isLocal linkEndpoints.1
              bendTerminalMem.2
              (by simpa using centerInterior)
              (Or.inl ⟨supportHorizontal,
                terminalSupportHorizontal⟩)
          exact incidentOfTerminal routeBend.outgoingTerminal
            bendTerminalMem.2 (by simp) keyEq
        · rcases
              drawingRouteBend_drawingPoint_snd_eq_portRow_of_adjacent_vertical
                isLocal (List.mem_dedup.mp routeBendMem)
                incomingVertical outgoingVertical with
            ⟨translateY, pointYEq⟩
          exact
            ((drawing_horizontal_interior_point_snd_ne_portRow
                firstIndexedMem link.first.translate
                (routeBend.drawingPoint graph)
                supportHorizontal centerInterior translateY)
              pointYEq).elim
    · rcases
          drawingRouteBend_incomingVertical_or_outgoingVertical
            wellFormed degree isLocal
            (List.mem_dedup.mp routeBendMem) with
        incomingVertical | outgoingVertical
      · have terminalSupportVertical :
            ((CarrierNode.terminal
              routeBend.incomingTerminal).supportingSegment
                graph).IsVertical := by
          simpa [CarrierNode.supportingSegment,
            CarrierNode.indexed, CarrierNode.translate,
            RouteBend.incomingTerminal] using
            (GridSegment.isVertical_translate
              (GridSegment.mk
                routeBend.incomingStart routeBend.bend)
              ((drawing graph).periodTranslation
                routeBend.translate)).mpr incomingVertical
        have keyEq :=
          retainedCarrierNode_carrierKey_eq_terminal_of_parallel_endpoint
            wellFormed degree isLocal linkEndpoints.1
            bendTerminalMem.1
            (by simpa using centerInterior)
            (Or.inr ⟨supportVertical,
              terminalSupportVertical⟩)
        exact incidentOfTerminal routeBend.incomingTerminal
          bendTerminalMem.1 (by simp) keyEq
      · have terminalSupportVertical :
            ((CarrierNode.terminal
              routeBend.outgoingTerminal).supportingSegment
                graph).IsVertical := by
          simpa [CarrierNode.supportingSegment,
            CarrierNode.indexed, CarrierNode.translate,
            RouteBend.outgoingTerminal] using
            (GridSegment.isVertical_translate
              (GridSegment.mk
                routeBend.bend routeBend.outgoingFinish)
              ((drawing graph).periodTranslation
                routeBend.translate)).mpr outgoingVertical
        have keyEq :=
          retainedCarrierNode_carrierKey_eq_terminal_of_parallel_endpoint
            wellFormed degree isLocal linkEndpoints.1
            bendTerminalMem.2
            (by simpa using centerInterior)
            (Or.inr ⟨supportVertical,
              terminalSupportVertical⟩)
        exact incidentOfTerminal routeBend.outgoingTerminal
          bendTerminalMem.2 (by simp) keyEq
  · rcases centerEndpoint with centerStart | centerFinish
    · let terminal : SegmentTerminal :=
        ⟨link.first.indexed, link.first.translate, .start⟩
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph :=
        mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
          graph terminal firstIndexedMem firstTranslateNeighbor
      have terminalPointEq :
          terminal.drawingPoint graph =
            routeBend.drawingPoint graph := by
        calc
          terminal.drawingPoint graph =
              (link.first.supportingSegment graph).start := by
                rfl
          _ = routeBend.drawingPoint graph := centerStart.symm
      have keyEq :
          link.first.carrierKey = terminal.carrierKey := by
        simp [terminal,
          CarrierNode.carrierKey_eq_indexed_translate,
          SegmentTerminal.carrierKey]
      exact incidentOfTerminal terminal terminalMem
        terminalPointEq keyEq
    · let terminal : SegmentTerminal :=
        ⟨link.first.indexed, link.first.translate, .finish⟩
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph :=
        mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
          graph terminal firstIndexedMem firstTranslateNeighbor
      have terminalPointEq :
          terminal.drawingPoint graph =
            routeBend.drawingPoint graph := by
        calc
          terminal.drawingPoint graph =
              (link.first.supportingSegment graph).finish := by
                rfl
          _ = routeBend.drawingPoint graph := centerFinish.symm
      have keyEq :
          link.first.carrierKey = terminal.carrierKey := by
        simp [terminal,
          CarrierNode.carrierKey_eq_indexed_translate,
          SegmentTerminal.carrierKey]
      exact incidentOfTerminal terminal terminalMem
        terminalPointEq keyEq

/-- The bend-overlap incidence theorem for selected representatives. -/
theorem
    retainedDrawingCompleteCarrierLink_incidentToRouteBend_of_macrocell_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈ (drawingRouteBends graph).dedup)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower
          (routeBend.drawingPoint graph))
        (planarSATMacrocellRouteUpper
          (routeBend.drawingPoint graph))) :
    CarrierLinkIncidentToRouteBend link routeBend :=
  retainedDrawingCompleteCarrierLinkRaw_incidentToRouteBend_of_macrocell_overlap
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1
      (retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph linkMem)
      routeBendMem notSeparated

/-- Every raw retained carrier route whose source translate lies in the
neighbor window avoids every route of every bend corner component, whether
the carrier is incident to the bend or geometrically separated from its
macrocell. -/
theorem
    retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        (PeriodicCNF.incidenceGraph formula))
    (firstTranslateNeighbor :
      IsNeighborTranslation link.first.translate)
    {routeBend : RouteBend}
    (routeBendMember :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {bendClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {bendClauseIndex : Nat}
    (bendClauseMember :
      (bendClause, bendClauseIndex) ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).formula.zipIdx)
    {bendLiteral : PlanarSATVariable Variable × Bool}
    {bendLiteralIndex : Nat}
    (bendLiteralMember :
      (bendLiteral, bendLiteralIndex) ∈
        bendClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATBendCornerIncidenceDrawing
        formula routeBend).routes
          bendClauseIndex bendLiteralIndex) := by
  by_cases incident :
      CarrierLinkIncidentToRouteBend link routeBend
  · exact
      retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther_of_raw_incident
        wellFormed degree isLocal linkMember routeBendMember incident
        carrierClauseMember carrierLiteralMember
        bendClauseMember bendLiteralMember
  · have rectanglesSeparated :
        ClosedGridRectanglesSeparated
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) link)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) link)
          (planarSATMacrocellRouteLower
            (routeBend.drawingPoint
              (PeriodicCNF.incidenceGraph formula)))
          (planarSATMacrocellRouteUpper
            (routeBend.drawingPoint
              (PeriodicCNF.incidenceGraph formula))) := by
      by_contra notSeparated
      exact incident
        (retainedDrawingCompleteCarrierLinkRaw_incidentToRouteBend_of_macrocell_overlap
          wellFormed degree isLocal linkMember firstTranslateNeighbor
          routeBendMember
          notSeparated)
    exact
      retainedDrawingPlanarSATCarrierRoute_avoids_macrocell_of_raw_rectanglesSeparated
        wellFormed degree isLocal linkMember
        carrierClauseMember carrierLiteralMember
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_bounded
          formula routeBend)
        bendClauseMember bendLiteralMember
        rectanglesSeparated

/-- The all-bend route-separation theorem for selected representatives. -/
theorem
    retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {routeBend : RouteBend}
    (routeBendMember :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {bendClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {bendClauseIndex : Nat}
    (bendClauseMember :
      (bendClause, bendClauseIndex) ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).formula.zipIdx)
    {bendLiteral : PlanarSATVariable Variable × Bool}
    {bendLiteralIndex : Nat}
    (bendLiteralMember :
      (bendLiteral, bendLiteralIndex) ∈
        bendClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATBendCornerIncidenceDrawing
        formula routeBend).routes
          bendClauseIndex bendLiteralIndex) :=
  retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther_of_raw
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph link).mp linkMember).1
      (retainedDrawingCompleteCarrierLink_first_translate_neighbor
        formula.incidenceGraph linkMember)
      routeBendMember carrierClauseMember carrierLiteralMember
      bendClauseMember bendLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
