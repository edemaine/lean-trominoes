import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry

/-!
# Routed-clause source-port geometry

Every incidence route leaves its clause vertex through one of the same three
left, middle, and right fanout ports used at variable vertices.  This file
identifies the source terminal's exact local and lifted positions and proves
that distinct incidences of one degree-three clause use distinct arms.

These results let a routed source clause instantiate the fixed planar
three-port star without relying on its presentation order.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

private theorem sourceTerminalFirstSegment
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    ((gridPolylineSegments
      (constructedEdgeRoute graph edge edgeIndex)).zipIdx.getD
        0 defaultTaggedGridSegment).1 =
      if vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
      then
        ⟨(vertexX (graph.vertices.idxOf edge.source), 2),
          (portX graph (sourcePort edge edgeIndex), 3)⟩
      else
        ⟨(vertexX (graph.vertices.idxOf edge.source), 2),
          (portX graph (sourcePort edge edgeIndex), 2)⟩ := by
  let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
  let sourceColumn := portX graph (sourcePort edge edgeIndex)
  by_cases same : sourceCenter = sourceColumn
  · simp [constructedEdgeRoute, joinPolylines, fanout,
      sourceCenter, sourceColumn, same, gridPolylineSegments]
  · simp [constructedEdgeRoute, joinPolylines, fanout,
      sourceCenter, sourceColumn, same, gridPolylineSegments]

set_option maxHeartbeats 1000000 in
/-- The local endpoint of a constructed source fanout is the left, middle,
or right port selected by the source-port rank. -/
theorem CNFRouteOccurrence.sourceTerminal_localPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    segmentTerminalLocalPosition
        (occurrence.sourceTerminal formula).indexed.segment
        (occurrence.sourceTerminal formula).endpoint =
      (targetDuplicatorArm
        (portRank (PeriodicCNF.incidenceGraph formula)
          (sourcePort occurrence.edge occurrence.edgeIndex))).portPosition := by
  let graph := PeriodicCNF.incidenceGraph formula
  let sourceCenter :=
    vertexX (graph.vertices.idxOf occurrence.edge.source)
  let sourceColumn :=
    portX graph (sourcePort occurrence.edge occurrence.edgeIndex)
  unfold CNFRouteOccurrence.sourceTerminal
    CNFRouteOccurrence.taggedSegments
  change segmentTerminalLocalPosition
      (((gridPolylineSegments
        (constructedEdgeRoute graph occurrence.edge
          occurrence.edgeIndex)).zipIdx.getD
            0 defaultTaggedGridSegment).1) .start =
    _
  rw [sourceTerminalFirstSegment]
  generalize rankEq :
      portRank graph
        (sourcePort occurrence.edge occurrence.edgeIndex) = rank
  cases rank with
  | zero =>
      have sourceColumnEq :
          sourceColumn = sourceCenter - 2 := by
        dsimp [sourceColumn, sourceCenter, portX]
        rw [rankEq]
        simp [sourcePort]
      have columnNe : sourceCenter ≠ sourceCenter - 2 := by
        omega
      simp [sourceCenter, sourceColumn, sourceColumnEq, columnNe,
        segmentTerminalLocalPosition,
        targetDuplicatorArm, DuplicatorArm.portPosition]
  | succ rank =>
      cases rank with
      | zero =>
          have sourceColumnEq :
              sourceColumn = sourceCenter := by
            dsimp [sourceColumn, sourceCenter, portX]
            rw [rankEq]
            simp [sourcePort]
          simp [sourceCenter, sourceColumn, sourceColumnEq,
            segmentTerminalLocalPosition,
            targetDuplicatorArm, DuplicatorArm.portPosition]
      | succ rank =>
          have sourceColumnEq :
              sourceColumn =
                sourceCenter + 2 * (rank : Int) + 2 := by
            dsimp [sourceColumn, sourceCenter, portX]
            rw [rankEq]
            simp [sourcePort]
            ring
          have columnGreater :
              sourceCenter <
                sourceCenter + 2 * (rank : Int) + 2 := by
            omega
          have columnNe :
              sourceCenter ≠
                sourceCenter + 2 * (rank : Int) + 2 :=
            ne_of_lt columnGreater
          simp [sourceCenter, sourceColumn, sourceColumnEq,
            columnNe, columnGreater, segmentTerminalLocalPosition,
            targetDuplicatorArm, DuplicatorArm.portPosition]

/-- Classifying a source terminal by its local coordinate recovers the arm
selected by its source-port rank. -/
theorem CNFRouteOccurrence.sourceTerminal_duplicatorArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    (occurrence.sourceTerminal formula).duplicatorArm =
      targetDuplicatorArm
        (portRank (PeriodicCNF.incidenceGraph formula)
          (sourcePort occurrence.edge occurrence.edgeIndex)) := by
  rw [SegmentTerminal.duplicatorArm,
    occurrence.sourceTerminal_localPosition formula]
  generalize portRank (PeriodicCNF.incidenceGraph formula)
      (sourcePort occurrence.edge occurrence.edgeIndex) = rank
  cases rank with
  | zero =>
      simp [targetDuplicatorArm, DuplicatorArm.portPosition]
  | succ rank =>
      cases rank with
      | zero =>
          simp [targetDuplicatorArm, DuplicatorArm.portPosition]
      | succ rank =>
          simp [targetDuplicatorArm, DuplicatorArm.portPosition]

/-- The drawing-grid point underlying a source terminal is the translated
source vertex of its constructed incidence route. -/
theorem CNFRouteOccurrence.sourceTerminal_drawingPoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    SegmentTerminal.drawingPoint
        (PeriodicCNF.incidenceGraph formula)
        (occurrence.sourceTerminal formula) =
      Cell.add
        (vertexPosition
          ((PeriodicCNF.incidenceGraph formula).vertices.idxOf
            occurrence.edge.source))
        (Cell.scale
          (drawingGridSize
            (PeriodicCNF.incidenceGraph formula) : Int)
          occurrence.translate) := by
  let graph := PeriodicCNF.incidenceGraph formula
  unfold CNFRouteOccurrence.sourceTerminal
    CNFRouteOccurrence.taggedSegments
    SegmentTerminal.drawingPoint
  change
    (GridSegment.translate
      ((drawing graph).periodTranslation occurrence.translate)
      ((gridPolylineSegments
        (constructedEdgeRoute graph occurrence.edge
          occurrence.edgeIndex)).zipIdx.getD
            0 defaultTaggedGridSegment).1).start =
      _
  rw [sourceTerminalFirstSegment]
  split_ifs <;>
    apply Prod.ext <;>
    simp [graph, GridSegment.translate,
      PeriodicGridDrawing.periodTranslation,
      drawing_gridSize, vertexPosition, Cell.add, Cell.scale] <;>
    ring

/-- A genuine indexed source terminal is the lifted position of the clause
occurrence named by its metadata. -/
theorem CNFRouteOccurrence.sourceTerminal_drawingPoint_eq_lifted
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (occurrence : CNFRouteOccurrence Variable)
    (edgeMember :
      (occurrence.edge, occurrence.edgeIndex) ∈
        (PeriodicCNF.incidenceGraph formula).edges.zipIdx) :
    SegmentTerminal.drawingPoint
        (PeriodicCNF.incidenceGraph formula)
        (occurrence.sourceTerminal formula) =
      liftedIncidenceVertexPosition formula
        (.clause occurrence.clauseOccurrence.1)
        occurrence.clauseOccurrence.2 := by
  let graph := PeriodicCNF.incidenceGraph formula
  have sourceMember :
      occurrence.edge.source ∈ graph.vertices :=
    (wellFormed.2 occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)).1
  have sourceEqual :
      occurrence.edge.source =
        .clause occurrence.clauseOccurrence.1 := by
    rfl
  rw [occurrence.sourceTerminal_drawingPoint formula]
  unfold liftedIncidenceVertexPosition
  rw [← sourceEqual]
  change
    Cell.add
        (vertexPosition (graph.vertices.idxOf occurrence.edge.source))
        (Cell.scale (drawingGridSize graph : Int)
          occurrence.translate) =
      Cell.add
        ((drawing graph).vertexPosition graph occurrence.edge.source)
        ((drawing graph).periodTranslation
          occurrence.clauseOccurrence.2)
  rw [drawing_vertexPosition_of_mem graph sourceMember]
  apply Prod.ext <;>
    simp [graph, CNFRouteOccurrence.clauseOccurrence,
      PeriodicGridDrawing.periodTranslation,
      drawing_gridSize, Cell.add, Cell.scale]

/-- At a selected clause site, its source terminal is exactly the
corresponding left, middle, or right port in the clause macrocell. -/
theorem CNFRouteOccurrence.sourceTerminal_position_eq_routedClausePort
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : ClauseRouteSite)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ clauseRouteOccurrencesAt formula site) :
    SegmentTerminal.position
        (PeriodicCNF.incidenceGraph formula)
        (occurrence.sourceTerminal formula) =
      Cell.add
        (liftedIncidenceVertexMacroOrigin formula
          (.clause site.1) site.2)
        ((occurrence.sourceTerminal formula).duplicatorArm.portPosition) := by
  have edgeMember :
      (occurrence.edge, occurrence.edgeIndex) ∈
        (PeriodicCNF.incidenceGraph formula).edges.zipIdx := by
    rcases List.mem_map.mp occurrenceMember with
      ⟨taggedIncidence, taggedIncidenceMember, occurrenceEqual⟩
    subst occurrence
    exact PeriodicCNF.tagged_incidence_edge_mem
      formula (List.mem_filter.mp taggedIncidenceMember).1
  have siteEqual :=
    clauseRouteOccurrencesAt_clauseOccurrence
      formula site occurrenceMember
  rw [SegmentTerminal.position,
    CNFRouteOccurrence.sourceTerminal_drawingPoint_eq_lifted
      formula wellFormed occurrence edgeMember,
    occurrence.sourceTerminal_localPosition formula,
    occurrence.sourceTerminal_duplicatorArm formula,
    siteEqual]
  unfold liftedIncidenceVertexMacroOrigin
  apply Prod.ext <;>
    simp [Cell.add, Cell.scale]

/-- The arm of a source occurrence, expressed without expanding its
terminal structure. -/
def sourceOccurrenceArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    DuplicatorArm :=
  targetDuplicatorArm
    (portRank (PeriodicCNF.incidenceGraph formula)
      (sourcePort occurrence.edge occurrence.edgeIndex))

@[simp] theorem sourceOccurrenceArm_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    sourceOccurrenceArm formula occurrence =
      (occurrence.sourceTerminal formula).duplicatorArm := by
  exact (occurrence.sourceTerminal_duplicatorArm formula).symm

private theorem targetDuplicatorArm_injective_below_three
    {first second : Nat}
    (firstLt : first < 3) (secondLt : second < 3)
    (equal :
      targetDuplicatorArm first =
        targetDuplicatorArm second) :
    first = second := by
  have firstCases :
      first = 0 ∨ first = 1 ∨ first = 2 := by
    omega
  have secondCases :
      second = 0 ∨ second = 1 ∨ second = 2 := by
    omega
  rcases firstCases with rfl | rfl | rfl <;>
    rcases secondCases with rfl | rfl | rfl <;>
    simp_all [targetDuplicatorArm]

private theorem clauseRouteOccurrencesAt_eq_of_edgeIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {first second : CNFRouteOccurrence Variable}
    (firstMember :
      first ∈ clauseRouteOccurrencesAt formula site)
    (secondMember :
      second ∈ clauseRouteOccurrencesAt formula site)
    (edgeIndexEqual : first.edgeIndex = second.edgeIndex) :
    first = second := by
  rcases List.mem_map.mp firstMember with
    ⟨firstTagged, firstTaggedMember, firstEqual⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondTagged, secondTaggedMember, secondEqual⟩
  subst first
  subst second
  have taggedEqual :
      firstTagged = secondTagged :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      (List.mem_filter.mp firstTaggedMember).1
      (List.mem_filter.mp secondTaggedMember).1
      edgeIndexEqual
  subst secondTagged
  rfl

/-- At one degree-three clause site, the physical arm identifies the routed
incidence occurrence. -/
theorem sourceOccurrenceArm_injective_on
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : ClauseRouteSite)
    {first second : CNFRouteOccurrence Variable}
    (firstMember :
      first ∈ clauseRouteOccurrencesAt formula site)
    (secondMember :
      second ∈ clauseRouteOccurrencesAt formula site)
    (armEqual :
      sourceOccurrenceArm formula first =
        sourceOccurrenceArm formula second) :
    first = second := by
  let graph := PeriodicCNF.incidenceGraph formula
  have firstEdgeMember :
      (first.edge, first.edgeIndex) ∈ graph.edges.zipIdx := by
    rcases List.mem_map.mp firstMember with
      ⟨tagged, taggedMember, firstEqual⟩
    subst first
    exact PeriodicCNF.tagged_incidence_edge_mem
      formula (List.mem_filter.mp taggedMember).1
  have secondEdgeMember :
      (second.edge, second.edgeIndex) ∈ graph.edges.zipIdx := by
    rcases List.mem_map.mp secondMember with
      ⟨tagged, taggedMember, secondEqual⟩
    subst second
    exact PeriodicCNF.tagged_incidence_edge_mem
      formula (List.mem_filter.mp taggedMember).1
  let firstPort := sourcePort first.edge first.edgeIndex
  let secondPort := sourcePort second.edge second.edgeIndex
  have firstRankLt :
      portRank graph firstPort < 3 :=
    portRank_lt_three degree
      (sourcePort_mem_allPorts graph firstEdgeMember)
  have secondRankLt :
      portRank graph secondPort < 3 :=
    portRank_lt_three degree
      (sourcePort_mem_allPorts graph secondEdgeMember)
  have rankEqual :
      portRank graph firstPort =
        portRank graph secondPort := by
    apply targetDuplicatorArm_injective_below_three
      firstRankLt secondRankLt
    exact armEqual
  have firstSite :=
    clauseRouteOccurrencesAt_clauseOccurrence
      formula site firstMember
  have secondSite :=
    clauseRouteOccurrencesAt_clauseOccurrence
      formula site secondMember
  have portVertexEqual :
      firstPort.vertex = secondPort.vertex := by
    change
      CNFVertex.clause first.clauseOccurrence.1 =
        CNFVertex.clause second.clauseOccurrence.1
    rw [firstSite, secondSite]
  have firstPortMember :
      firstPort ∈ portsAt graph firstPort.vertex :=
    sourcePort_mem_portsAt graph firstEdgeMember
  have portEqual : firstPort = secondPort := by
    apply (List.idxOf_inj firstPortMember).mp
    change
      (portsAt graph firstPort.vertex).idxOf firstPort =
        (portsAt graph secondPort.vertex).idxOf secondPort
      at rankEqual
    simpa [portVertexEqual] using rankEqual
  apply clauseRouteOccurrencesAt_eq_of_edgeIndex_eq
    formula site firstMember secondMember
  exact congrArg GraphPort.edgeIndex portEqual

/-- The arm list of one routed degree-three clause has no duplicates. -/
theorem sourceOccurrenceArms_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : ClauseRouteSite) :
    ((clauseRouteOccurrencesAt formula site).map
      (sourceOccurrenceArm formula)).Nodup := by
  apply (clauseRouteOccurrencesAt_nodup formula site).map_on
  intro first firstMember second secondMember armEqual
  exact sourceOccurrenceArm_injective_on
    formula degree site firstMember secondMember armEqual

end PeriodicOrthocrossing
end LeanTrominoes
