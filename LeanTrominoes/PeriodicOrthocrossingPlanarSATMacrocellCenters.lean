import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellBounds
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Centers of planar-SAT macrocells

The non-carrier local drawings are indexed by points in the infinite
periodic lift of the constructed incidence drawing.  This file begins the
site-classification part of their separation proof by showing that a lifted
graph-vertex position uniquely determines both its protovertex and its
periodic translate.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Two points in the open fundamental square have unique periodic
translates in the infinite lift. -/
theorem translatedFundamentalPositions_eq
    (drawing : PeriodicGridDrawing)
    {first second firstTranslate secondTranslate : Cell}
    (firstBounds : drawing.PositionInFundamentalSquare first)
    (secondBounds : drawing.PositionInFundamentalSquare second)
    (equal :
      Cell.add first (drawing.periodTranslation firstTranslate) =
        Cell.add second (drawing.periodTranslation secondTranslate)) :
    first = second ∧ firstTranslate = secondTranslate := by
  have relativeEqual :
      first =
        Cell.add second
          (drawing.periodTranslation
            (Cell.sub secondTranslate firstTranslate)) := by
    rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
    rcases secondTranslate with
      ⟨secondTranslateX, secondTranslateY⟩
    simp only [Cell.add, Cell.sub,
      PeriodicGridDrawing.periodTranslation,
      Cell.scale, Prod.mk.injEq] at equal ⊢
    constructor
    · linear_combination equal.1
    · linear_combination equal.2
  have positionsEqual : first = second := by
    by_contra different
    exact
      PositionedPeriodicCNF.fundamentalPosition_ne_translated
        drawing firstBounds secondBounds different relativeEqual
  subst second
  have translationsEqual :
      drawing.periodTranslation firstTranslate =
        drawing.periodTranslation secondTranslate :=
    Cell.add_left_injective first equal
  have periodPositive :
      (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  refine ⟨rfl, ?_⟩
  rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
  rcases secondTranslate with
    ⟨secondTranslateX, secondTranslateY⟩
  simp only [PeriodicGridDrawing.periodTranslation,
    Cell.scale, Prod.mk.injEq] at translationsEqual
  apply Prod.ext
  · nlinarith [translationsEqual.1]
  · nlinarith [translationsEqual.2]

end PeriodicGridDrawing

namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The constructed drawing position of any declared protovertex lies in
the open fundamental square. -/
theorem drawing_vertexPosition_in_fundamental_square
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices) :
    (drawing graph).PositionInFundamentalSquare
      ((drawing graph).vertexPosition graph vertex) := by
  rw [drawing_vertexPosition_of_mem graph vertexMember]
  have indexLt :
      graph.vertices.idxOf vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare,
    vertexPosition, vertexX, drawing_gridSize, drawingGridSize]
  omega

/-- A lifted constructed-drawing vertex position uniquely determines both
the declared protovertex and its lattice translate. -/
theorem liftedDrawingVertexPosition_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {firstVertex secondVertex : Vertex}
    (firstVertexMember : firstVertex ∈ graph.vertices)
    (secondVertexMember : secondVertex ∈ graph.vertices)
    {firstTranslate secondTranslate : Cell}
    (equal :
      Cell.add
          ((drawing graph).vertexPosition graph firstVertex)
          ((drawing graph).periodTranslation firstTranslate) =
        Cell.add
          ((drawing graph).vertexPosition graph secondVertex)
          ((drawing graph).periodTranslation secondTranslate)) :
    firstVertex = secondVertex ∧
      firstTranslate = secondTranslate := by
  have data :=
    (drawing graph).translatedFundamentalPositions_eq
      (drawing_vertexPosition_in_fundamental_square
        graph firstVertexMember)
      (drawing_vertexPosition_in_fundamental_square
        graph secondVertexMember)
      equal
  have indexEqual :
      graph.vertices.idxOf firstVertex =
        graph.vertices.idxOf secondVertex := by
    apply vertexPosition_injective
    simpa only [
      drawing_vertexPosition_of_mem graph firstVertexMember,
      drawing_vertexPosition_of_mem graph secondVertexMember] using
      data.1
  exact
    ⟨(List.idxOf_inj firstVertexMember).mp indexEqual,
      data.2⟩

/-- The constructed orthocrossing drawing has at most one canonical
crossover record at any drawing-grid point. -/
theorem orientedCrossing_eq_of_point_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossings graph)
    (secondMem : second ∈ orientedCrossings graph)
    (pointEqual : first.point = second.point) :
    first = second := by
  have firstSound := orientedCrossings_sound graph firstMem
  have secondSound := orientedCrossings_sound graph secondMem
  have firstOccurrenceEqual :
      PeriodicGridDrawing.SegmentOccurrenceKey
          first.first first.firstTranslate =
        PeriodicGridDrawing.SegmentOccurrenceKey
          second.first second.firstTranslate := by
    by_contra occurrenceDifferent
    have proper :=
      drawing_isOrthocrossing wellFormed degree isLocal
        first.first firstSound.1
        second.first secondSound.1
        first.firstTranslate second.firstTranslate first.point
        occurrenceDifferent
        firstSound.2.2.2.2.1.2.2.1
        (by
          rw [pointEqual]
          exact secondSound.2.2.2.2.1.2.2.1)
    have firstHorizontal :=
      firstSound.2.2.2.2.2.1
    have secondHorizontal :=
      secondSound.2.2.2.2.2.1
    rcases proper.2.2 with
      horizontalVertical | verticalHorizontal
    · exact secondHorizontal.2 horizontalVertical.2.1
    · exact firstHorizontal.2 verticalHorizontal.1.1
  have firstIndexedEqual :
      first.first = second.first := by
    apply indexedSegment_eq_of_indices_eq (drawing graph)
      firstSound.1 secondSound.1
    · exact congrArg Prod.fst firstOccurrenceEqual
    · exact congrArg
        (fun key => key.2.1) firstOccurrenceEqual
  have firstTranslateEqual :
      first.firstTranslate = second.firstTranslate :=
    congrArg (fun key => key.2.2) firstOccurrenceEqual
  exact
    orientedCrossing_eq_of_firstOccurrence_eq_of_point_eq
      wellFormed degree isLocal firstMem secondMem
      firstIndexedEqual firstTranslateEqual pointEqual

/-- Every represented lifted clause site names a declared incidence-graph
clause vertex.  This also covers empty clauses, which have no incidence
edge witnessing their vertex. -/
theorem drawingClauseRouteSite_vertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : ClauseRouteSite}
    (siteMem : site ∈ drawingClauseRouteSites formula) :
    CNFVertex.clause site.1 ∈
      (PeriodicCNF.incidenceGraph formula).vertices := by
  rcases List.mem_flatMap.mp siteMem with
    ⟨taggedClause, taggedClauseMem, translateMem⟩
  rcases List.mem_map.mp translateMem with
    ⟨translate, translateMem, siteEqual⟩
  subst site
  apply List.mem_append_right
  simp only [PeriodicCNF.incidenceClauseVertices, List.mem_map]
  exact
    ⟨taggedClause.2,
      List.mem_range.mpr
        (List.snd_lt_of_mem_zipIdx taggedClauseMem),
      rfl⟩

/-- Every represented lifted variable site names a declared
incidence-graph variable vertex. -/
theorem drawingVariableRouteSite_vertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    CNFVertex.variable site.1 ∈
      (PeriodicCNF.incidenceGraph formula).vertices := by
  rw [drawingVariableRouteSites, List.mem_dedup] at siteMem
  rcases List.mem_map.mp siteMem with
    ⟨occurrence, occurrenceMem, siteEqual⟩
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem,
      translatedOccurrenceMem⟩
  rcases List.mem_map.mp translatedOccurrenceMem with
    ⟨translate, translateMem, occurrenceEqual⟩
  subst occurrence
  subst site
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      formula taggedIncidenceMem
  have endpoints :=
    (PeriodicCNF.incidenceGraph_isWellFormed formula).2
      taggedIncidence.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  simpa only [CNFRouteOccurrence.variableOccurrence,
    CNFIncidence.edge_target] using endpoints.2

/-- Every neighboring metadata-rich route occurrence retains its matching
tagged incidence-graph edge. -/
theorem CNFRouteOccurrence.edge_mem_of_mem_drawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (occurrence.edge, occurrence.edgeIndex) ∈
      (PeriodicCNF.incidenceGraph formula).edges.zipIdx := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem,
      translatedOccurrenceMem⟩
  rcases List.mem_map.mp translatedOccurrenceMem with
    ⟨translate, translateMem, occurrenceEqual⟩
  subst occurrence
  exact
    PeriodicCNF.tagged_incidence_edge_mem
      formula taggedIncidenceMem

/-- On the only target-port ranks allowed by degree three, the geometric
duplicator-arm classifier is injective. -/
theorem targetDuplicatorArm_injective_below_three
    {firstRank secondRank : Nat}
    (firstLt : firstRank < 3)
    (secondLt : secondRank < 3)
    (armEqual :
      targetDuplicatorArm firstRank =
        targetDuplicatorArm secondRank) :
    firstRank = secondRank := by
  interval_cases firstRank <;>
    interval_cases secondRank <;>
    simp_all [targetDuplicatorArm]

/-- At one represented variable site, two active links with the same
physical arm are the same link. -/
theorem routedVariableLinksAt_eq_of_duplicatorArm_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : VariableRouteSite Variable)
    {first second : EqualityLink (PlanarSATNode Variable)}
    (firstMem : first ∈ routedVariableLinksAt formula site)
    (secondMem : second ∈ routedVariableLinksAt formula site)
    (armEqual :
      first.first.duplicatorArm =
        second.first.duplicatorArm) :
    first = second := by
  have linkArmEqual := armEqual
  have firstNodeMem :
      first.first ∈ routedVariableNodes formula site := by
    rcases List.mem_map.mp firstMem with
      ⟨taggedNode, taggedNodeMem, linkEqual⟩
    subst first
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  have secondNodeMem :
      second.first ∈ routedVariableNodes formula site := by
    rcases List.mem_map.mp secondMem with
      ⟨taggedNode, taggedNodeMem, linkEqual⟩
    subst second
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  rcases (mem_routedVariableNodes_iff
      formula site first.first).mp firstNodeMem with
    ⟨firstOccurrence, firstOccurrenceAtMem, firstNodeEqual⟩
  rcases (mem_routedVariableNodes_iff
      formula site second.first).mp secondNodeMem with
    ⟨secondOccurrence, secondOccurrenceAtMem, secondNodeEqual⟩
  have firstData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site firstOccurrenceAtMem
  have secondData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site secondOccurrenceAtMem
  have firstEdgeMem :=
    firstOccurrence.edge_mem_of_mem_drawing formula firstData.1
  have secondEdgeMem :=
    secondOccurrence.edge_mem_of_mem_drawing formula secondData.1
  let graph := PeriodicCNF.incidenceGraph formula
  let firstPort :=
    targetPort firstOccurrence.edge firstOccurrence.edgeIndex
  let secondPort :=
    targetPort secondOccurrence.edge secondOccurrence.edgeIndex
  have firstPortMem : firstPort ∈ allPorts graph :=
    targetPort_mem_allPorts graph firstEdgeMem
  have secondPortMem : secondPort ∈ allPorts graph :=
    targetPort_mem_allPorts graph secondEdgeMem
  rw [firstNodeEqual, secondNodeEqual] at armEqual
  change
    (firstOccurrence.targetTerminal formula).duplicatorArm =
      (secondOccurrence.targetTerminal formula).duplicatorArm
    at armEqual
  rw [firstOccurrence.targetTerminal_duplicatorArm formula,
    secondOccurrence.targetTerminal_duplicatorArm formula] at armEqual
  have rankEqual :
      portRank graph firstPort =
        portRank graph secondPort := by
    apply targetDuplicatorArm_injective_below_three
    · exact portRank_lt_three degree firstPortMem
    · exact portRank_lt_three degree secondPortMem
    · exact armEqual
  have targetVertexEqual :
      firstPort.vertex = secondPort.vertex := by
    have atomEqual :
        firstOccurrence.incidence.literal.atom =
          secondOccurrence.incidence.literal.atom :=
      congrArg Prod.fst
        (firstData.2.trans secondData.2.symm)
    dsimp [firstPort, secondPort]
    change
      CNFVertex.variable
          firstOccurrence.incidence.literal.atom =
        CNFVertex.variable
          secondOccurrence.incidence.literal.atom
    exact congrArg CNFVertex.variable atomEqual
  have portXEqual :
      portX graph firstPort = portX graph secondPort := by
    unfold portX
    rw [targetVertexEqual, rankEqual]
  have portEqual : firstPort = secondPort :=
    portX_injective_on_allPorts
      wellFormed degree firstPortMem secondPortMem portXEqual
  have edgeIndexEqual :
      firstOccurrence.edgeIndex =
        secondOccurrence.edgeIndex :=
    congrArg GraphPort.edgeIndex portEqual
  have taggedEdgeEqual :
      (firstOccurrence.edge, firstOccurrence.edgeIndex) =
        (secondOccurrence.edge, secondOccurrence.edgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstEdgeMem secondEdgeMem edgeIndexEqual
  have edgeEqual :
      firstOccurrence.edge = secondOccurrence.edge :=
    congrArg Prod.fst taggedEdgeEqual
  have translatedTargetEqual :
      Cell.add firstOccurrence.translate
          firstOccurrence.edge.offset =
        Cell.add secondOccurrence.translate
          secondOccurrence.edge.offset := by
    exact congrArg Prod.snd
      (firstData.2.trans secondData.2.symm)
  rw [edgeEqual] at translatedTargetEqual
  have translateEqual :
      firstOccurrence.translate =
        secondOccurrence.translate := by
    have xEqual :=
      congrArg Prod.fst translatedTargetEqual
    have yEqual :=
      congrArg Prod.snd translatedTargetEqual
    apply Prod.ext
    · simp only [Cell.add] at xEqual
      omega
    · simp only [Cell.add] at yEqual
      omega
  have occurrenceEqual :
      firstOccurrence = secondOccurrence :=
    drawingCNFRouteOccurrences_eq_of_edgeIndex_eq_of_translate_eq
      formula firstData.1 secondData.1
      edgeIndexEqual translateEqual
  have firstEndpointEqual :
      first.first = second.first :=
    firstNodeEqual.trans
      ((congrArg
        (fun occurrence =>
          PlanarSATNode.carrier
            (CarrierNode.terminal
              (occurrence.targetTerminal formula)))
        occurrenceEqual).trans secondNodeEqual.symm)
  have secondEndpointEqual :
      first.second = second.second :=
    (routedVariableLinksAt_second formula site firstMem).trans
      (routedVariableLinksAt_second
        formula site secondMem).symm
  have positionsEqual :
      first.positions = second.positions := by
    rw [routedVariableLink_positions formula site firstMem,
      routedVariableLink_positions formula site secondMem,
      linkArmEqual]
  rcases first with ⟨firstFirst, firstSecond, firstPositions⟩
  rcases second with ⟨secondFirst, secondSecond, secondPositions⟩
  simp only at firstEndpointEqual secondEndpointEqual positionsEqual
  subst secondFirst
  subst secondSecond
  subst secondPositions
  rfl

/-- Equal lifted positions of two represented clause sites force the
entire site keys to agree. -/
theorem liftedClauseRouteSite_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : ClauseRouteSite}
    (firstMem : first ∈ drawingClauseRouteSites formula)
    (secondMem : second ∈ drawingClauseRouteSites formula)
    (equal :
      liftedIncidenceVertexPosition formula
          (.clause first.1) first.2 =
        liftedIncidenceVertexPosition formula
          (.clause second.1) second.2) :
    first = second := by
  have data :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingClauseRouteSite_vertex_mem formula firstMem)
      (drawingClauseRouteSite_vertex_mem formula secondMem)
      equal
  have clauseIndexEqual : first.1 = second.1 := by
    exact CNFVertex.clause.inj data.1
  exact Prod.ext clauseIndexEqual data.2

/-- Equal lifted positions of two represented variable sites force the
entire site keys to agree. -/
theorem liftedVariableRouteSite_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : VariableRouteSite Variable}
    (firstMem : first ∈ drawingVariableRouteSites formula)
    (secondMem : second ∈ drawingVariableRouteSites formula)
    (equal :
      liftedIncidenceVertexPosition formula
          (.variable first.1) first.2 =
        liftedIncidenceVertexPosition formula
          (.variable second.1) second.2) :
    first = second := by
  have data :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingVariableRouteSite_vertex_mem formula firstMem)
      (drawingVariableRouteSite_vertex_mem formula secondMem)
      equal
  have variableEqual : first.1 = second.1 := by
    exact CNFVertex.variable.inj data.1
  exact Prod.ext variableEqual data.2

/-- A represented lifted clause site and represented lifted variable site
cannot occupy the same drawing-grid point. -/
theorem liftedClauseRouteSite_ne_liftedVariableRouteSite
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseSite : ClauseRouteSite}
    {variableSite : VariableRouteSite Variable}
    (clauseMem :
      clauseSite ∈ drawingClauseRouteSites formula)
    (variableMem :
      variableSite ∈ drawingVariableRouteSites formula) :
    liftedIncidenceVertexPosition formula
        (.clause clauseSite.1) clauseSite.2 ≠
      liftedIncidenceVertexPosition formula
        (.variable variableSite.1) variableSite.2 := by
  intro equal
  have data :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingClauseRouteSite_vertex_mem formula clauseMem)
      (drawingVariableRouteSite_vertex_mem formula variableMem)
      equal
  cases data.1

end PeriodicOrthocrossing
end LeanTrominoes
