/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteSoundness
import LeanTrominoes.PeriodicCNFPlanarSATClauseIndex
import LeanTrominoes.PeriodicCNFPlanarSATGeometry
import LeanTrominoes.PlanarThreeSATDuplicatorArm

/-!
# Routed-variable target-port geometry

Every incidence route enters its target variable macrocell through one of
three fanout ports.  This file identifies that physical arm from the target
port rank and proves that the terminal and the corresponding equality arm
use exactly the same position.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The geometric duplicator arm selected by a target-port rank.  Ranks
beyond the first two all lie on the right fanout branch; the degree-three
hypothesis used later ensures that only rank two is active. -/
def targetDuplicatorArm : Nat → DuplicatorArm
  | 0 => .left
  | 1 => .middle
  | _ => .right

private theorem gridPolylineSegments_joinPolylines_target
    {first second : List Cell} {boundary : Cell}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    gridPolylineSegments (joinPolylines first second) =
      gridPolylineSegments first ++
        gridPolylineSegments second := by
  induction first using List.twoStepInduction with
  | nil =>
      simp at firstLast
  | singleton first =>
      cases second with
      | nil => simp at secondHead
      | cons head tail =>
          simp only [List.getLast?_singleton,
            Option.some.injEq] at firstLast
          simp only [List.head?_cons,
            Option.some.injEq] at secondHead
          subst first
          subst head
          simp [joinPolylines, gridPolylineSegments]
  | cons_cons first next rest _ tailInduction =>
      have tailLast :
          (next :: rest).getLast? = some boundary := by
        simpa using firstLast
      have tailSegments :=
        tailInduction next tailLast
      simpa [joinPolylines, gridPolylineSegments,
        tailSegments, List.cons_append]

private theorem zipIdx_getLastD_fst
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

private theorem getLastD_append_right
    {α : Type*} (first second : List α)
    (secondNonempty : second ≠ []) (default : α) :
    (first ++ second).getLastD default =
      second.getLastD default := by
  cases second with
  | nil => exact (secondNonempty rfl).elim
  | cons second rest =>
      induction first with
      | nil => rfl
      | cons first tail induction =>
          cases tail <;> simp_all

private theorem gridPolylineSegments_getLastD_finish
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

set_option maxHeartbeats 1000000 in
/-- The local endpoint of a constructed target fanout is the port belonging
to its rank-selected duplicator arm. -/
theorem CNFRouteOccurrence.targetTerminal_localPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    segmentTerminalLocalPosition
        (occurrence.targetTerminal formula).indexed.segment
        (occurrence.targetTerminal formula).endpoint =
      (targetDuplicatorArm
        (portRank (PeriodicCNF.incidenceGraph formula)
          (targetPort occurrence.edge occurrence.edgeIndex))).portPosition := by
  let graph := PeriodicCNF.incidenceGraph formula
  let sourceCenter :=
    vertexX (graph.vertices.idxOf occurrence.edge.source)
  let targetCenter :=
    vertexX (graph.vertices.idxOf occurrence.edge.target)
  let sourceColumn :=
    portX graph (sourcePort occurrence.edge occurrence.edgeIndex)
  let targetColumn :=
    portX graph (targetPort occurrence.edge occurrence.edgeIndex)
  let targetTranslate :=
    Cell.scale (drawingGridSize graph : Int)
      occurrence.edge.offset
  let sourceFanout := fanout sourceCenter sourceColumn
  let core :=
    edgeCore graph occurrence.edge occurrence.edgeIndex
  let targetFanout :=
    translatePolyline targetTranslate
      (fanout targetCenter targetColumn).reverse
  let targetBoundaryPoint : Cell :=
    Cell.add targetTranslate (targetColumn, 3)
  have sourceBoundary :
      sourceFanout.getLast? = core.head? := by
    simp [sourceFanout, core, sourceColumn]
  have targetBoundary :
      core.getLast? = some targetBoundaryPoint := by
    dsimp [core, targetBoundaryPoint,
      targetTranslate, targetColumn]
    rw [edgeCore_getLast?]
    simp [Cell.add, add_comm]
  have targetFanoutHead :
      targetFanout.head? = some targetBoundaryPoint := by
    dsimp [targetFanout, targetBoundaryPoint,
      targetTranslate, targetCenter, targetColumn]
    by_cases same :
        vertexX (graph.vertices.idxOf occurrence.edge.target) =
          portX graph
            (targetPort occurrence.edge occurrence.edgeIndex)
    · simp [translatePolyline, fanout, same,
        Cell.add, add_comm]
    · simp [translatePolyline, fanout, same,
        Cell.add, add_comm]
  have innerBoundary :
      (joinPolylines sourceFanout core).getLast? =
        some targetBoundaryPoint := by
    rw [joinPolylines_getLast?_of_second
      (edgeCore_length_ge_two graph occurrence.edge
        occurrence.edgeIndex)]
    exact targetBoundary
  have routeSegments :
      gridPolylineSegments
          (constructedEdgeRoute graph occurrence.edge
            occurrence.edgeIndex) =
        gridPolylineSegments
            (joinPolylines sourceFanout core) ++
          gridPolylineSegments targetFanout := by
    rw [show constructedEdgeRoute graph occurrence.edge
        occurrence.edgeIndex =
          joinPolylines
            (joinPolylines sourceFanout core)
            targetFanout by
      rfl]
    exact gridPolylineSegments_joinPolylines_target
      innerBoundary targetFanoutHead
  unfold CNFRouteOccurrence.targetTerminal
    CNFRouteOccurrence.taggedSegments
  change segmentTerminalLocalPosition
      (((gridPolylineSegments
        (constructedEdgeRoute graph occurrence.edge
          occurrence.edgeIndex)).zipIdx.getLastD
            defaultTaggedGridSegment).1) .finish =
    _
  rw [routeSegments, zipIdx_getLastD_fst]
  have targetSegmentsNonempty :
      gridPolylineSegments targetFanout ≠ [] := by
    dsimp [targetFanout]
    by_cases same : targetCenter = targetColumn
    · simp [fanout, same, translatePolyline,
        gridPolylineSegments]
    · simp [fanout, same, translatePolyline,
        gridPolylineSegments]
  rw [getLastD_append_right
    (gridPolylineSegments (joinPolylines sourceFanout core))
    (gridPolylineSegments targetFanout)
    targetSegmentsNonempty]
  generalize rankEq :
      portRank graph
        (targetPort occurrence.edge occurrence.edgeIndex) = rank
  cases rank with
  | zero =>
      have targetColumnEq :
          targetColumn = targetCenter - 2 := by
        dsimp [targetColumn, targetCenter, portX]
        rw [rankEq]
        simp [targetPort]
      have columnNe : targetCenter ≠ targetCenter - 2 := by
        omega
      simp [targetFanout, targetColumnEq, columnNe,
        targetDuplicatorArm, DuplicatorArm.portPosition,
        fanout, translatePolyline, gridPolylineSegments,
        segmentTerminalLocalPosition, Cell.add]
  | succ rank =>
      cases rank with
      | zero =>
          have targetColumnEq :
              targetColumn = targetCenter := by
            dsimp [targetColumn, targetCenter, portX]
            rw [rankEq]
            simp [targetPort]
          simp [targetFanout, targetColumnEq,
            targetDuplicatorArm, DuplicatorArm.portPosition,
            fanout, translatePolyline, gridPolylineSegments,
            segmentTerminalLocalPosition, Cell.add]
      | succ rank =>
          have targetColumnEq :
              targetColumn =
                targetCenter + 2 * (rank : Int) + 2 := by
            dsimp [targetColumn, targetCenter, portX]
            rw [rankEq]
            simp [targetPort]
            ring
          have columnGreater :
              targetCenter <
                targetCenter + 2 * (rank : Int) + 2 := by
            omega
          have columnNe :
              targetCenter ≠
                targetCenter + 2 * (rank : Int) + 2 :=
            ne_of_lt columnGreater
          simp [targetFanout, targetColumnEq, columnNe,
            columnGreater,
            targetDuplicatorArm, DuplicatorArm.portPosition,
            fanout, translatePolyline, gridPolylineSegments,
            segmentTerminalLocalPosition, Cell.add]
          exact columnGreater.le

/-- Classifying the target terminal by its local coordinate recovers the
same arm selected by the target-port rank. -/
theorem CNFRouteOccurrence.targetTerminal_duplicatorArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    (occurrence.targetTerminal formula).duplicatorArm =
      targetDuplicatorArm
        (portRank (PeriodicCNF.incidenceGraph formula)
          (targetPort occurrence.edge occurrence.edgeIndex)) := by
  rw [SegmentTerminal.duplicatorArm,
    occurrence.targetTerminal_localPosition formula]
  generalize portRank (PeriodicCNF.incidenceGraph formula)
      (targetPort occurrence.edge occurrence.edgeIndex) = rank
  cases rank with
  | zero =>
      simp [targetDuplicatorArm, DuplicatorArm.portPosition]
  | succ rank =>
      cases rank with
      | zero =>
          simp [targetDuplicatorArm, DuplicatorArm.portPosition]
      | succ rank =>
          simp [targetDuplicatorArm, DuplicatorArm.portPosition]

private irreducible_def targetTerminalDrawingPoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) : Cell :=
  SegmentTerminal.drawingPoint
    (PeriodicCNF.incidenceGraph formula)
    (occurrence.targetTerminal formula)

private irreducible_def expectedTargetTerminalDrawingPoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) : Cell :=
  Cell.add
    (vertexPosition
      ((PeriodicCNF.incidenceGraph formula).vertices.idxOf
        occurrence.edge.target))
    (Cell.scale
      (drawingGridSize
        (PeriodicCNF.incidenceGraph formula) : Int)
      (Cell.add occurrence.translate occurrence.edge.offset))

set_option maxHeartbeats 800000 in
private theorem targetTerminalDrawingPoint_eq_expected
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    targetTerminalDrawingPoint formula occurrence =
      expectedTargetTerminalDrawingPoint formula occurrence := by
  let graph := PeriodicCNF.incidenceGraph formula
  let route :=
    constructedEdgeRoute graph occurrence.edge
      occurrence.edgeIndex
  have routeLast :
      route.getLast? =
        some (Cell.add
          (vertexPosition
            (graph.vertices.idxOf occurrence.edge.target))
          (Cell.scale (drawingGridSize graph : Int)
            occurrence.edge.offset)) := by
    exact constructedEdgeRoute_getLast?
      graph occurrence.edge occurrence.edgeIndex
  have routeNonempty : route ≠ [] := by
    intro routeEmpty
    simp [routeEmpty] at routeLast
  have routeLong : 2 ≤ route.length := by
    dsimp [route]
    unfold constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf occurrence.edge.source))
        (portX graph
          (sourcePort occurrence.edge occurrence.edgeIndex))
    omega
  have routeSegmentsNonempty :
      gridPolylineSegments route ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    rw [gridPolylineSegments_length] at lengthZero
    simp only [List.length_nil] at lengthZero
    omega
  have segmentFinish :
      (((gridPolylineSegments route).zipIdx.getLastD
          defaultTaggedGridSegment).1).finish =
        route.getLastD (0, 0) := by
    rw [zipIdx_getLastD_fst]
    exact gridPolylineSegments_getLastD_finish
      route routeSegmentsNonempty
        defaultTaggedGridSegment.1 (0, 0)
  have routeLastD :
      route.getLastD (0, 0) =
        Cell.add
          (vertexPosition
            (graph.vertices.idxOf occurrence.edge.target))
          (Cell.scale (drawingGridSize graph : Int)
            occurrence.edge.offset) := by
    cases routeEq : route with
    | nil =>
        exact (routeNonempty routeEq).elim
    | cons first rest =>
        cases rest with
        | nil =>
            simpa [routeEq, List.getLast?_cons] using routeLast
        | cons second rest =>
            simpa [routeEq, List.getLast?_cons] using routeLast
  rw [targetTerminalDrawingPoint_def,
    expectedTargetTerminalDrawingPoint_def]
  unfold CNFRouteOccurrence.targetTerminal
    CNFRouteOccurrence.taggedSegments
    SegmentTerminal.drawingPoint
  dsimp only [GridSegment.translate]
  rw [show constructedEdgeRoute
      (PeriodicCNF.incidenceGraph formula)
      occurrence.edge occurrence.edgeIndex = route by
    rfl]
  rw [segmentFinish, routeLastD]
  apply Prod.ext <;>
    simp [graph,
      PeriodicGridDrawing.periodTranslation,
      drawing_gridSize,
      Cell.add, Cell.scale] <;>
    ring

/-- The drawing-grid point underlying a target terminal is the translated
target vertex of its constructed incidence route. -/
theorem CNFRouteOccurrence.targetTerminal_drawingPoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    SegmentTerminal.drawingPoint
        (PeriodicCNF.incidenceGraph formula)
        (occurrence.targetTerminal formula) =
      Cell.add
        (vertexPosition
          ((PeriodicCNF.incidenceGraph formula).vertices.idxOf
            occurrence.edge.target))
        (Cell.scale
          (drawingGridSize
            (PeriodicCNF.incidenceGraph formula) : Int)
          (Cell.add occurrence.translate occurrence.edge.offset)) := by
  simpa only [targetTerminalDrawingPoint_def,
    expectedTargetTerminalDrawingPoint_def] using
      targetTerminalDrawingPoint_eq_expected formula occurrence

/-- For an enumerated incidence route, the target terminal's drawing point
is the lifted position of the variable occurrence named by its metadata. -/
theorem CNFRouteOccurrence.targetTerminal_drawingPoint_eq_lifted
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    SegmentTerminal.drawingPoint
        (PeriodicCNF.incidenceGraph formula)
        (occurrence.targetTerminal formula) =
      liftedIncidenceVertexPosition formula
        (.variable occurrence.variableOccurrence.1)
        occurrence.variableOccurrence.2 := by
  let graph := PeriodicCNF.incidenceGraph formula
  have edgeMem :=
    occurrence.taggedEdge_mem formula occurrenceMem
  have targetMem :
      occurrence.edge.target ∈ graph.vertices :=
    (wellFormed.2 occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMem)).2
  have targetEq :
      occurrence.edge.target =
        .variable occurrence.variableOccurrence.1 := by
    simp [CNFRouteOccurrence.edge,
      CNFRouteOccurrence.variableOccurrence]
  rw [occurrence.targetTerminal_drawingPoint formula]
  unfold liftedIncidenceVertexPosition
  rw [← targetEq]
  change
    Cell.add
        (vertexPosition (graph.vertices.idxOf occurrence.edge.target))
        (Cell.scale (drawingGridSize graph : Int)
          (Cell.add occurrence.translate occurrence.edge.offset)) =
      Cell.add
        ((drawing graph).vertexPosition graph occurrence.edge.target)
        ((drawing graph).periodTranslation
          occurrence.variableOccurrence.2)
  rw [drawing_vertexPosition_of_mem graph targetMem]
  apply Prod.ext <;>
    simp [graph, CNFRouteOccurrence.variableOccurrence,
      CNFRouteOccurrence.edge,
      PeriodicGridDrawing.periodTranslation,
      drawing_gridSize, Cell.add, Cell.scale]

/-- At a selected variable site, the constructed target terminal and its
active equality arm have exactly the same macro-grid endpoint. -/
theorem CNFRouteOccurrence.targetTerminal_position_eq_routedVariableArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ variableRouteOccurrencesAt formula site) :
    SegmentTerminal.position
        (PeriodicCNF.incidenceGraph formula)
        (occurrence.targetTerminal formula) =
      Cell.add (routedVariableOrigin formula site)
        ((occurrence.targetTerminal formula).duplicatorArm.portPosition) := by
  have selected :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMem
  rw [SegmentTerminal.position,
    occurrence.targetTerminal_drawingPoint_eq_lifted
      formula wellFormed selected.1,
    occurrence.targetTerminal_localPosition formula,
    occurrence.targetTerminal_duplicatorArm formula,
    ← selected.2]
  rfl

/-- The external endpoint of an active equality link is placed at the
fanout arm classified from that terminal's actual geometry. -/
theorem routedVariableLink_first_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    drawingPlanarSATVariablePosition formula (.inl link.first) =
      Cell.add (routedVariableOrigin formula site)
        link.first.duplicatorArm.portPosition := by
  have firstMem :
      link.first ∈ routedVariableNodes formula site := by
    rcases List.mem_map.mp linkMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst link
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  rcases (mem_routedVariableNodes_iff
      formula site link.first).mp firstMem with
    ⟨occurrence, occurrenceMem, firstEq⟩
  rw [firstEq]
  simpa [drawingPlanarSATVariablePosition,
    CarrierNode.position, PlanarSATNode.duplicatorArm] using
    occurrence.targetTerminal_position_eq_routedVariableArm
      formula wellFormed site occurrenceMem

/-- The internal endpoint of every active equality link is the common
fanout-aligned center of its routed-variable macrocell. -/
theorem routedVariableLink_second_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    drawingPlanarSATVariablePosition formula (.inl link.second) =
      Cell.add (routedVariableOrigin formula site)
        duplicatorArmCenterPosition := by
  rw [routedVariableLinksAt_second formula site linkMem]
  rfl

/-- The terminal and center endpoints of an active routed-variable arm are
distinct logical nodes. -/
theorem routedVariableLink_first_ne_second
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    link.first ≠ link.second := by
  have firstMem :
      link.first ∈ routedVariableNodes formula site := by
    rcases List.mem_map.mp linkMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst link
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  rcases (mem_routedVariableNodes_iff
      formula site link.first).mp firstMem with
    ⟨occurrence, occurrenceMem, firstEq⟩
  rw [firstEq,
    routedVariableLinksAt_second formula site linkMem]
  simp

end PeriodicOrthocrossing
end LeanTrominoes
