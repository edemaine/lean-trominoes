import LeanTrominoes.PeriodicOrthocrossingVertical
import Mathlib.Tactic.Ring

/-!
# Uniqueness of vertical segment interiors

Active vertical lanes identify their semantic roles.  Their vertical spans
are at most one drawing period, so two translates of the same open segment
cannot overlap unless their vertical cell translations also agree.  Together
these facts identify the complete indexed occurrence key.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Every vertical piece of a local constructed route has vertical span at
most one drawing period, in either endpoint order. -/
theorem classifiedSegment_vertical_span_le_period
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    (edgeLocal : edge.span ≤ 1)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (vertical : classified.segment.IsVertical) :
    classified.segment.finish.2 - classified.segment.start.2 ≤
        drawingGridSize graph ∧
      classified.segment.start.2 - classified.segment.finish.2 ≤
        drawingGridSize graph := by
  have tracks := edgeTrack_bounds graph edgeMem
  have tracks' :
      3 < edgeTrack edgeIndex ∧
        edgeTrack edgeIndex + 1 < drawingGridSize graph := by
    simpa using tracks
  have periodPositive := drawingGridSize_pos graph
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsVertical →
          item.segment.finish.2 - item.segment.start.2 ≤
              drawingGridSize graph ∧
            item.segment.start.2 - item.segment.finish.2 ≤
              drawingGridSize graph := by
    intro item itemMem itemVertical
    by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at itemMem
      subst item
      simp
      omega
    · simp [classifiedSourceFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [GridSegment.IsVertical] at itemVertical
      · simp
        omega
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsVertical →
          item.segment.finish.2 - item.segment.start.2 ≤
              drawingGridSize graph ∧
            item.segment.start.2 - item.segment.finish.2 ≤
              drawingGridSize graph := by
    rcases offset_eq_of_span_le_one edge edgeLocal with
      offsetZero | offsetRight | offsetLeft | offsetUp | offsetDown
    · simp [classifiedEdgeCore, offsetZero,
        GridSegment.IsVertical, Cell.add, Cell.scale]
      omega
    · simp [classifiedEdgeCore, offsetRight,
        GridSegment.IsVertical, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    · simp [classifiedEdgeCore, offsetLeft,
        GridSegment.IsVertical, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    · simp [classifiedEdgeCore, offsetUp,
        GridSegment.IsVertical, Cell.add, Cell.scale]
      omega
    · simp [classifiedEdgeCore, offsetDown,
        GridSegment.IsVertical, Cell.add, Cell.scale]
      omega
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsVertical →
          item.segment.finish.2 - item.segment.start.2 ≤
              drawingGridSize graph ∧
            item.segment.start.2 - item.segment.finish.2 ≤
              drawingGridSize graph := by
    intro item itemMem itemVertical
    by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at itemMem
      subst item
      simp [Cell.add, Cell.scale]
      omega
    · simp [classifiedTargetFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [Cell.add, Cell.scale]
        omega
      · simp [GridSegment.IsVertical, Cell.add, Cell.scale]
          at itemVertical
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceClassified =>
        sourceAll classified sourceClassified vertical)
      (fun coreClassified =>
        coreAll classified coreClassified vertical))
    (fun targetClassified =>
      targetAll classified targetClassified vertical)

/-- Vertical interior containment exposes strict containment of the point's
vertical coordinate between the segment endpoints. -/
theorem strictlyBetween_y_of_interiorContains_of_isVertical
    {segment : GridSegment} {point : Cell}
    (contains : segment.InteriorContains point)
    (vertical : segment.IsVertical) :
    GridSegment.StrictlyBetween
      segment.start.2 segment.finish.2 point.2 := by
  rcases contains with
    ⟨horizontal, _, _⟩ | ⟨_, _, between⟩
  · exact (vertical.2 horizontal.1).elim
  · exact between

/-- Once equal normalized columns have identified equal semantic roles,
common vertical interiors determine the same route, classified segment, and
cell translate. -/
theorem vertical_classified_occurrences_unique_of_roles_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {firstRoute secondRoute :
      (PeriodicEdge Vertex × Nat) × Nat}
    (firstRouteMem : firstRoute ∈ graph.edges.zipIdx.zipIdx)
    (secondRouteMem : secondRoute ∈ graph.edges.zipIdx.zipIdx)
    {firstClassified secondClassified :
      ClassifiedSegment Vertex × Nat}
    (firstClassifiedMem :
      firstClassified ∈
        (classifiedRouteSegments graph
          firstRoute.1.1 firstRoute.1.2).zipIdx)
    (secondClassifiedMem :
      secondClassified ∈
        (classifiedRouteSegments graph
          secondRoute.1.1 secondRoute.1.2).zipIdx)
    {firstTranslate secondTranslate point : Cell}
    (firstContains :
      (firstClassified.1.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          point)
    (secondContains :
      (secondClassified.1.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          point)
    (firstVertical :
      (firstClassified.1.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsVertical)
    (secondVertical :
      (secondClassified.1.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsVertical)
    (rolesEqual :
      firstClassified.1.role = secondClassified.1.role) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        ⟨firstRoute.2, firstClassified.2,
          firstClassified.1.segment⟩ firstTranslate =
      PeriodicGridDrawing.SegmentOccurrenceKey
        ⟨secondRoute.2, secondClassified.2,
          secondClassified.1.segment⟩ secondTranslate := by
  have firstClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx firstClassifiedMem
  have secondClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx secondClassifiedMem
  have firstRoleIndex :=
    classifiedSegment_role_edgeIndex firstClassifiedMem'
  have secondRoleIndex :=
    classifiedSegment_role_edgeIndex secondClassifiedMem'
  have firstNested := nested_zipIdx_indices_eq firstRouteMem
  have secondNested := nested_zipIdx_indices_eq secondRouteMem
  have routeIndicesEqual : firstRoute.2 = secondRoute.2 := by
    rw [← firstNested, ← secondNested]
    rw [← firstRoleIndex, ← secondRoleIndex]
    exact congrArg SegmentRole.edgeIndex rolesEqual
  have routesEqual :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstRouteMem secondRouteMem routeIndicesEqual
  subst secondRoute
  have classifiedEqual :=
    taggedClassified_eq_of_role_eq
      firstClassifiedMem secondClassifiedMem rolesEqual
  subst secondClassified
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have lanesEqual :=
    vertical_lanes_eq_of_interior_contains
      firstContains secondContains firstVertical secondVertical
  have lanesEqual' :
      firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 =
        firstClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using lanesEqual
  have translatedColumnsEqual :
      (drawingGridSize graph : Int) * firstTranslate.1 =
        drawingGridSize graph * secondTranslate.1 :=
    Int.add_left_cancel lanesEqual'
  have translateXEqual :
      firstTranslate.1 = secondTranslate.1 :=
    mul_left_cancel₀
      (ne_of_gt periodPositive) translatedColumnsEqual
  have storedVertical :
      firstClassified.1.segment.IsVertical :=
    (GridSegment.isVertical_translate _ _).mp firstVertical
  have edgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have edgeLocal :
      firstRoute.1.1.span ≤ 1 :=
    isLocal firstRoute.1.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  have span :=
    classifiedSegment_vertical_span_le_period
      edgeMem edgeLocal firstClassifiedMem' storedVertical
  have firstBetween :=
    strictlyBetween_y_of_interiorContains_of_isVertical
      firstContains firstVertical
  have secondBetween :=
    strictlyBetween_y_of_interiorContains_of_isVertical
      secondContains secondVertical
  have firstBetween' :
      GridSegment.StrictlyBetween
        (firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstTranslate.2)
        (firstClassified.1.segment.finish.2 +
          drawingGridSize graph * firstTranslate.2)
        point.2 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using firstBetween
  have secondBetween' :
      GridSegment.StrictlyBetween
        (firstClassified.1.segment.start.2 +
          drawingGridSize graph * secondTranslate.2)
        (firstClassified.1.segment.finish.2 +
          drawingGridSize graph * secondTranslate.2)
        point.2 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using secondBetween
  have translateYEqual :=
    strictlyBetween_periodic_shifts_unique
      periodPositive span.1 span.2 firstBetween' secondBetween'
  have translatesEqual : firstTranslate = secondTranslate := by
    apply Prod.ext
    · exact translateXEqual
    · exact translateYEqual
  subst secondTranslate
  rfl

/-- Two vertical segment occurrences in the constructed drawing cannot have
a common interior point unless their indexed occurrence keys agree. -/
theorem drawing_hasUniqueVerticalInteriors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ∀ first ∈ (drawing graph).indexedSegments,
      ∀ second ∈ (drawing graph).indexedSegments,
        ∀ firstTranslate secondTranslate point,
          (first.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).InteriorContains
              point →
          (second.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).InteriorContains
              point →
          (first.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).IsVertical →
          (second.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).IsVertical →
          PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate := by
  intro first firstMem second secondMem
    firstTranslate secondTranslate point
    firstContains secondContains firstVertical secondVertical
  rcases exists_classifiedSegment_of_drawing_mem firstMem with
    ⟨firstRoute, firstRouteMem,
      firstClassified, firstClassifiedMem, firstEq⟩
  rcases exists_classifiedSegment_of_drawing_mem secondMem with
    ⟨secondRoute, secondRouteMem,
      secondClassified, secondClassifiedMem, secondEq⟩
  subst first
  subst second
  have firstEdgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have secondEdgeMem :
      (secondRoute.1.1, secondRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx secondRouteMem
  have firstClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx firstClassifiedMem
  have secondClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx secondClassifiedMem
  have firstActive :=
    classifiedSegment_activeVertical_of_interiorContains
      firstClassifiedMem' firstTranslate point
        firstContains firstVertical
  have secondActive :=
    classifiedSegment_activeVertical_of_interiorContains
      secondClassifiedMem' secondTranslate point
        secondContains secondVertical
  have firstLane :=
    classifiedSegment_vertical_lane
      firstClassifiedMem' firstActive
  have secondLane :=
    classifiedSegment_vertical_lane
      secondClassifiedMem' secondActive
  have translatedLanesEqual :=
    vertical_lanes_eq_of_interior_contains
      firstContains secondContains firstVertical secondVertical
  have translatedLanesEqual' :
      firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 =
        secondClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using translatedLanesEqual
  have normalizedLanesEqual :
      verticalLaneBase graph firstClassified.1.role +
          drawingGridSize graph *
            (verticalLaneCellShift
              firstRoute.1.1 firstClassified.1.role +
              firstTranslate.1) =
        verticalLaneBase graph secondClassified.1.role +
          drawingGridSize graph *
            (verticalLaneCellShift
              secondRoute.1.1 secondClassified.1.role +
              secondTranslate.1) := by
    calc
      _ = firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 := by
            rw [firstLane]
            ring
      _ = secondClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 :=
            translatedLanesEqual'
      _ = _ := by
        rw [secondLane]
        ring
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have firstLaneBounds :=
    verticalLaneBase_bounds
      wellFormed degree firstEdgeMem firstClassifiedMem' firstActive
  have secondLaneBounds :=
    verticalLaneBase_bounds
      wellFormed degree secondEdgeMem secondClassifiedMem' secondActive
  have normalizedLaneData :=
    periodic_coordinate_unique
      periodPositive firstLaneBounds secondLaneBounds normalizedLanesEqual
  have rolesEqual :=
    activeVertical_roles_eq_of_lanes_eq
      wellFormed degree firstEdgeMem secondEdgeMem
      firstClassifiedMem' secondClassifiedMem'
      firstActive secondActive normalizedLaneData.1
  exact vertical_classified_occurrences_unique_of_roles_eq
    isLocal
    firstRouteMem secondRouteMem
    firstClassifiedMem secondClassifiedMem
    firstContains secondContains firstVertical secondVertical
    rolesEqual

end PeriodicOrthocrossing
end LeanTrominoes
