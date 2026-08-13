/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingHorizontal
import Mathlib.Tactic.Ring

/-!
# Uniqueness of horizontal segment interiors

Private track rows identify their owning protoedge.  The shared fanout row is
handled separately by the unique midpoint of each noncentral port.  Together,
these invariants show that two horizontal segment occurrences with a common
interior point are the same indexed occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- A horizontal fanout role names a port with the endpoint kind appropriate
to the source or target side on which that role occurs. -/
def SegmentRole.HorizontalFanoutEndCorrect {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourceFanoutHorizontal port => port.endKind = .source
  | .targetFanoutHorizontal port => port.endKind = .target
  | _ => True

theorem classifiedSegment_horizontalFanoutEndCorrect
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex) :
    classified.role.HorizontalFanoutEndCorrect := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.HorizontalFanoutEndCorrect := by
    simp [classifiedSourceFanout,
      SegmentRole.HorizontalFanoutEndCorrect, sourcePort]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.HorizontalFanoutEndCorrect := by
    simp [classifiedEdgeCore, SegmentRole.HorizontalFanoutEndCorrect]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.HorizontalFanoutEndCorrect := by
    simp [classifiedTargetFanout,
      SegmentRole.HorizontalFanoutEndCorrect, targetPort]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem => sourceAll classified sourceMem)
      (fun coreMem => coreAll classified coreMem))
    (fun targetMem => targetAll classified targetMem)

/-- Equal real ports force equal source/target fanout roles. -/
theorem horizontalFanout_roles_eq_of_ports_eq
    {Vertex : Type*}
    {firstRole secondRole : SegmentRole Vertex}
    {firstPort secondPort : GraphPort Vertex}
    (firstFanout : firstRole.IsHorizontalFanout)
    (secondFanout : secondRole.IsHorizontalFanout)
    (firstPortEq :
      firstRole.horizontalFanoutPort = some firstPort)
    (secondPortEq :
      secondRole.horizontalFanoutPort = some secondPort)
    (firstEnd : firstRole.HorizontalFanoutEndCorrect)
    (secondEnd : secondRole.HorizontalFanoutEndCorrect)
    (portsEqual : firstPort = secondPort) :
    firstRole = secondRole := by
  cases firstRole <;> cases secondRole <;>
    simp_all [SegmentRole.IsHorizontalFanout,
      SegmentRole.horizontalFanoutPort,
      SegmentRole.HorizontalFanoutEndCorrect]

/-- The normalized midpoint coordinate of a fanout role is the coordinate of
the real port named by that role. -/
theorem fanoutMidpointBase_eq_of_horizontalFanoutPort
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {role : SegmentRole Vertex} {port : GraphPort Vertex}
    (portEq : role.horizontalFanoutPort = some port) :
    fanoutMidpointBase graph role =
      vertexX (graph.vertices.idxOf port.vertex) +
        (portRank graph port : Int) - 1 := by
  cases role <;>
    simp_all [SegmentRole.horizontalFanoutPort, fanoutMidpointBase]

/-- Once equal lanes have identified equal semantic roles, common horizontal
interiors determine the same route, classified segment, and cell translate. -/
theorem horizontal_classified_occurrences_unique_of_roles_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
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
    (firstHorizontal :
      (firstClassified.1.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsHorizontal)
    (secondHorizontal :
      (secondClassified.1.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsHorizontal)
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
    horizontal_lanes_eq_of_interior_contains
      firstContains secondContains firstHorizontal secondHorizontal
  have lanesEqual' :
      firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstTranslate.2 =
        firstClassified.1.segment.start.2 +
          drawingGridSize graph * secondTranslate.2 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using lanesEqual
  have translatedRowsEqual :
      (drawingGridSize graph : Int) * firstTranslate.2 =
        drawingGridSize graph * secondTranslate.2 :=
    Int.add_left_cancel lanesEqual'
  have translateYEqual :
      firstTranslate.2 = secondTranslate.2 :=
    mul_left_cancel₀ (ne_of_gt periodPositive) translatedRowsEqual
  have storedHorizontal :
      firstClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp firstHorizontal
  have edgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have edgeLocal :
      firstRoute.1.1.span ≤ 1 :=
    isLocal firstRoute.1.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  have span :=
    classifiedSegment_horizontal_span_le_period
      wellFormed degree edgeMem edgeLocal firstClassifiedMem'
        storedHorizontal
  have firstBetween :=
    strictlyBetween_x_of_interiorContains_of_isHorizontal
      firstContains firstHorizontal
  have secondBetween :=
    strictlyBetween_x_of_interiorContains_of_isHorizontal
      secondContains secondHorizontal
  have firstBetween' :
      GridSegment.StrictlyBetween
        (firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1)
        (firstClassified.1.segment.finish.1 +
          drawingGridSize graph * firstTranslate.1)
        point.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using firstBetween
  have secondBetween' :
      GridSegment.StrictlyBetween
        (firstClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1)
        (firstClassified.1.segment.finish.1 +
          drawingGridSize graph * secondTranslate.1)
        point.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using secondBetween
  have translateXEqual :=
    strictlyBetween_periodic_shifts_unique
      periodPositive span.1 span.2 firstBetween' secondBetween'
  have translatesEqual : firstTranslate = secondTranslate := by
    apply Prod.ext
    · exact translateXEqual
    · exact translateYEqual
  subst secondTranslate
  rfl

/-- Two horizontal segment occurrences in the constructed drawing cannot
have a common interior point unless their indexed occurrence keys agree. -/
theorem drawing_hasUniqueHorizontalInteriors
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
            ((drawing graph).periodTranslation firstTranslate)).IsHorizontal →
          (second.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).IsHorizontal →
          PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate := by
  intro first firstMem second secondMem
    firstTranslate secondTranslate point
    firstContains secondContains firstHorizontal secondHorizontal
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
  have firstStoredHorizontal :
      firstClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp firstHorizontal
  have secondStoredHorizontal :
      secondClassified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp secondHorizontal
  have firstHorizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      firstClassifiedMem' firstStoredHorizontal
  have secondHorizontalRole :=
    classifiedSegment_horizontalRole_of_isHorizontal
      secondClassifiedMem' secondStoredHorizontal
  have firstLane :=
    classifiedSegment_horizontal_lane
      firstClassifiedMem' firstHorizontalRole
  have secondLane :=
    classifiedSegment_horizontal_lane
      secondClassifiedMem' secondHorizontalRole
  have translatedLanesEqual :=
    horizontal_lanes_eq_of_interior_contains
      firstContains secondContains firstHorizontal secondHorizontal
  have translatedLanesEqual' :
      firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstTranslate.2 =
        secondClassified.1.segment.start.2 +
          drawingGridSize graph * secondTranslate.2 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using translatedLanesEqual
  have normalizedLanesEqual :
      horizontalLaneBase firstClassified.1.role +
          drawingGridSize graph *
            (horizontalLaneCellShift
              firstRoute.1.1 firstClassified.1.role +
              firstTranslate.2) =
        horizontalLaneBase secondClassified.1.role +
          drawingGridSize graph *
            (horizontalLaneCellShift
              secondRoute.1.1 secondClassified.1.role +
              secondTranslate.2) := by
    calc
      _ = firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstTranslate.2 := by
            rw [firstLane]
            ring
      _ = secondClassified.1.segment.start.2 +
          drawingGridSize graph * secondTranslate.2 :=
            translatedLanesEqual'
      _ = _ := by
        rw [secondLane]
        ring
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have firstLaneBounds :=
    horizontalLaneBase_bounds
      firstEdgeMem firstClassifiedMem' firstHorizontalRole
  have secondLaneBounds :=
    horizontalLaneBase_bounds
      secondEdgeMem secondClassifiedMem' secondHorizontalRole
  have normalizedLaneData :=
    periodic_coordinate_unique
      periodPositive firstLaneBounds secondLaneBounds normalizedLanesEqual
  rcases horizontal_roles_eq_or_both_fanout
      firstHorizontalRole secondHorizontalRole normalizedLaneData.1 with
    rolesEqual | ⟨firstFanout, secondFanout⟩
  · exact horizontal_classified_occurrences_unique_of_roles_eq
      wellFormed degree isLocal
      firstRouteMem secondRouteMem
      firstClassifiedMem secondClassifiedMem
      firstContains secondContains firstHorizontal secondHorizontal
      rolesEqual
  · rcases horizontalFanout_midpoint_of_interiorContains
        degree firstEdgeMem firstClassifiedMem'
          firstFanout firstTranslate point firstContains with
      ⟨firstPort, firstPortEq, firstPortMem, firstPoint⟩
    rcases horizontalFanout_midpoint_of_interiorContains
        degree secondEdgeMem secondClassifiedMem'
          secondFanout secondTranslate point secondContains with
      ⟨secondPort, secondPortEq, secondPortMem, secondPoint⟩
    have firstBaseEq :
        fanoutMidpointBase graph firstClassified.1.role =
          vertexX (graph.vertices.idxOf firstPort.vertex) +
            (portRank graph firstPort : Int) - 1 := by
      exact fanoutMidpointBase_eq_of_horizontalFanoutPort
        graph firstPortEq
    have secondBaseEq :
        fanoutMidpointBase graph secondClassified.1.role =
          vertexX (graph.vertices.idxOf secondPort.vertex) +
            (portRank graph secondPort : Int) - 1 := by
      exact fanoutMidpointBase_eq_of_horizontalFanoutPort
        graph secondPortEq
    have firstPoint' :
        point.1 =
          fanoutMidpointBase graph firstClassified.1.role +
            drawingGridSize graph *
              ((horizontalFanoutCellShift
                firstRoute.1.1 firstClassified.1.role).1 +
                firstTranslate.1) := by
      rw [firstBaseEq]
      calc
        _ = vertexX (graph.vertices.idxOf firstPort.vertex) +
              (portRank graph firstPort : Int) - 1 +
              drawingGridSize graph *
                (horizontalFanoutCellShift
                  firstRoute.1.1 firstClassified.1.role).1 +
              drawingGridSize graph * firstTranslate.1 :=
            firstPoint
        _ = _ := by ring
    have secondPoint' :
        point.1 =
          fanoutMidpointBase graph secondClassified.1.role +
            drawingGridSize graph *
              ((horizontalFanoutCellShift
                secondRoute.1.1 secondClassified.1.role).1 +
                secondTranslate.1) := by
      rw [secondBaseEq]
      calc
        _ = vertexX (graph.vertices.idxOf secondPort.vertex) +
              (portRank graph secondPort : Int) - 1 +
              drawingGridSize graph *
                (horizontalFanoutCellShift
                  secondRoute.1.1 secondClassified.1.role).1 +
              drawingGridSize graph * secondTranslate.1 :=
            secondPoint
        _ = _ := by ring
    have firstBaseBounds :=
      fanoutMidpointBase_bounds
        wellFormed degree firstPortEq firstPortMem
    have secondBaseBounds :=
      fanoutMidpointBase_bounds
        wellFormed degree secondPortEq secondPortMem
    have midpointData :=
      periodic_coordinate_unique
        periodPositive firstBaseBounds secondBaseBounds
          (firstPoint'.symm.trans secondPoint')
    have portsEqual :=
      horizontalFanoutPort_eq_of_midpoint_eq
        wellFormed degree firstPortEq secondPortEq
          firstPortMem secondPortMem midpointData.1
    have firstEnd :=
      classifiedSegment_horizontalFanoutEndCorrect firstClassifiedMem'
    have secondEnd :=
      classifiedSegment_horizontalFanoutEndCorrect secondClassifiedMem'
    have rolesEqual :=
      horizontalFanout_roles_eq_of_ports_eq
        firstFanout secondFanout firstPortEq secondPortEq
          firstEnd secondEnd portsEqual
    exact horizontal_classified_occurrences_unique_of_roles_eq
      wellFormed degree isLocal
      firstRouteMem secondRouteMem
      firstClassifiedMem secondClassifiedMem
      firstContains secondContains firstHorizontal secondHorizontal
      rolesEqual

end PeriodicOrthocrossing
end LeanTrominoes
