/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineSymmetries
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationOrdering
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-!
# Canonical incidence drawings under variable gauges

A variable gauge leaves every displayed literal occurrence fixed, but it can
change the first-literal anchor of each clause.  Consequently a canonical
clause-to-variable route is represented after gauging by translating the
entire old route through the difference between the old and new clause
anchors.  This translation is always a whole physical period.

This file defines that canonical route transport and proves that the
infinite periodic route arrangement is unchanged.  In particular, global
relative route separation survives an arbitrary per-variable gauge.
-/

namespace LeanTrominoes

namespace CNFIncidence

/-- Apply a variable gauge to the clause and literal metadata of one
syntactic incidence without changing either presentation index. -/
def variableGauge
    {Variable : Type*}
    (gauge : Variable → Cell)
    (incidence : CNFIncidence Variable) : CNFIncidence Variable :=
  ⟨incidence.clauseIndex,
    incidence.clause.variableGauge gauge,
    incidence.literalIndex,
    incidence.literal.variableGauge gauge⟩

end CNFIncidence

namespace PeriodicCNF

/-- Variable gauging maps the metadata-rich incidence enumeration
pointwise, preserving its clause-major and literal-minor indices. -/
theorem incidencesWithMetadata_variableGauge
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    incidencesWithMetadata (source.variableGauge gauge) =
      (incidencesWithMetadata source).map
        (CNFIncidence.variableGauge gauge) := by
  unfold incidencesWithMetadata PeriodicCNF.variableGauge
  rw [List.zipIdx_map]
  simp only [List.flatMap_map, Prod.map, id_eq]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp [PeriodicClause.variableGauge, List.zipIdx_map,
    List.map_map, CNFIncidence.variableGauge,
    Function.comp_def]

end PeriodicCNF

namespace PositionedPeriodicCNF

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- Semantic lattice shift which changes an old canonical clause route into
the canonical route for the variable-gauged clause. -/
def variableGaugeCanonicalRouteShift
    {Variable : Type*}
    (gauge : Variable → Cell)
    (clause : PositionedPeriodicClause Variable) : Cell :=
  Cell.sub
    (PeriodicCNF.clauseAnchor clause.literals)
    (PeriodicCNF.clauseAnchor
      (clause.literals.variableGauge gauge))

/-- The canonical gauged clause position is the old canonical position
translated by the route's whole-period gauge shift. -/
theorem canonicalClausePosition_variableGauge
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (clause : PositionedPeriodicClause Variable) :
    canonicalClausePosition
        (placement.variableGauge gauge)
        ⟨clause.position,
          clause.literals.variableGauge gauge⟩ =
      Cell.add
        (placement.translation
          (variableGaugeCanonicalRouteShift gauge clause))
        (canonicalClausePosition placement clause) := by
  rcases clause with ⟨⟨clauseX, clauseY⟩, literals⟩
  cases oldAnchorEq : PeriodicCNF.clauseAnchor literals with
  | mk oldAnchorX oldAnchorY =>
  cases newAnchorEq : PeriodicCNF.clauseAnchor
      (literals.variableGauge gauge) with
  | mk newAnchorX newAnchorY =>
  apply Prod.ext <;>
    simp [canonicalClausePosition,
      variableGaugeCanonicalRouteShift,
      PeriodicVariablePlacement.variableGauge,
      PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale,
      oldAnchorEq, newAnchorEq] <;>
    ring

/-- The translated old literal endpoint is exactly the canonical endpoint
specified by the gauged placement and gauged incidence edge. -/
theorem canonicalLiteralEndpoint_variableGauge
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (clause : PeriodicClause Variable)
    (literal : PeriodicLiteral Variable) :
    Cell.add
        (placement.translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor clause)
            (PeriodicCNF.clauseAnchor
              (clause.variableGauge gauge))))
        (Cell.add
          (placement.position literal.atom)
          (placement.translation
            (Cell.sub literal.offset
              (PeriodicCNF.clauseAnchor clause)))) =
      Cell.add
        ((placement.variableGauge gauge).position literal.atom)
        ((placement.variableGauge gauge).translation
          (Cell.sub
            (literal.variableGauge gauge).offset
            (PeriodicCNF.clauseAnchor
              (clause.variableGauge gauge)))) := by
  rcases literal with
    ⟨atom, ⟨literalX, literalY⟩, value⟩
  cases positionEq : placement.position atom with
  | mk positionX positionY =>
  cases gaugeEq : gauge atom with
  | mk gaugeX gaugeY =>
  cases oldAnchorEq : PeriodicCNF.clauseAnchor clause with
  | mk oldAnchorX oldAnchorY =>
  cases newAnchorEq : PeriodicCNF.clauseAnchor
      (clause.variableGauge gauge) with
  | mk newAnchorX newAnchorY =>
  apply Prod.ext <;>
    simp [PeriodicVariablePlacement.variableGauge,
      PeriodicVariablePlacement.translation,
      PeriodicLiteral.variableGauge,
      Cell.add, Cell.sub, Cell.scale,
      positionEq, gaugeEq] <;>
    ring

/-- Transport canonical incidence routes through a variable gauge.  Values
outside the finite clause presentation remain harmless empty routes. -/
def variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (variableGaugeCanonicalRouteShift gauge clause))
          (routes clauseIndex literalIndex)

/-- At a genuine source clause index, gauged canonical route lookup is the
advertised whole-period translation. -/
theorem variableGaugeCanonicalIncidenceRoutes_of_clause_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes clauseIndex literalIndex =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (variableGaugeCanonicalRouteShift gauge clause))
        (routes clauseIndex literalIndex) := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  simp [variableGaugeCanonicalIncidenceRoutes, clauseLookup]

/-- The drawing-level endpoint predicate exposes canonical endpoints for
one tagged syntactic incidence without requiring the other compatibility
fields of a planar presentation. -/
theorem incidenceRoutes_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (routes tagged.1.clauseIndex tagged.1.literalIndex).head? =
        some
          (incidenceVertexPositionAt source placement
            (.clause tagged.1.clauseIndex)) ∧
      (routes tagged.1.clauseIndex tagged.1.literalIndex).getLast? =
        some (Cell.add
          (placement.position tagged.1.literal.atom)
          ((incidenceDrawing source placement routes).periodTranslation
            tagged.1.edge.offset)) := by
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase taggedMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source.erase
  have endpointMembers :=
    graphWellFormed.2 tagged.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have endpoints := routesMatch
    (tagged.1.edge, tagged.2) edgeMember
  rw [incidenceDrawing_edgeRoute_of_tagged
      source placement routes taggedMember] at endpoints
  rw [incidenceDrawing_vertexPosition_of_mem
      source placement routes endpointMembers.1,
    incidenceDrawing_vertexPosition_of_mem
      source placement routes endpointMembers.2] at endpoints
  simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge,
    incidenceVertexPositionAt] using endpoints

/-- Gauged canonical routes have the exact endpoints prescribed by the
gauged incidence graph. -/
theorem variableGaugeCanonicalIncidenceRoutes_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    let gaugedIncidence := tagged.1.variableGauge gauge
    (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes
        gaugedIncidence.clauseIndex
        gaugedIncidence.literalIndex).head? =
        some
          (incidenceVertexPositionAt
            (source.variableGauge gauge)
            (placement.variableGauge gauge)
            (.clause gaugedIncidence.clauseIndex)) ∧
      (variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes
          gaugedIncidence.clauseIndex
          gaugedIncidence.literalIndex).getLast? =
        some (Cell.add
          ((placement.variableGauge gauge).position
            gaugedIncidence.literal.atom)
          ((incidenceDrawing
            (source.variableGauge gauge)
            (placement.variableGauge gauge)
            (variableGaugeCanonicalIncidenceRoutes
              source placement gauge routes)).periodTranslation
                gaugedIncidence.edge.offset)) := by
  dsimp only
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember,
      taggedEq⟩
  have oldEndpoints :=
    incidenceRoutes_endpoints_of_tagged
      source placement routes routesMatch taggedMember
  have clauseIndexLt :
      tagged.1.clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have clauseAt :
      source.clauses[tagged.1.clauseIndex] = clause :=
    (List.mem_zipIdx' clauseMember).2.symm
  have gaugedClauseIndexLt :
      tagged.1.clauseIndex <
        (source.variableGauge gauge).clauses.length := by
    simpa [PositionedPeriodicCNF.variableGauge]
      using clauseIndexLt
  have gaugedClauseAt :
      (source.variableGauge gauge).clauses[
          tagged.1.clauseIndex] =
        ⟨clause.position,
          clause.literals.variableGauge gauge⟩ := by
    simp [PositionedPeriodicCNF.variableGauge,
      List.getElem_map, clauseAt]
  have routeEq :=
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes clauseMember
      (literalIndex := tagged.1.literalIndex)
  change
    (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes
        tagged.1.clauseIndex tagged.1.literalIndex).head? = _ ∧
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes
        tagged.1.clauseIndex tagged.1.literalIndex).getLast? = _
  rw [routeEq]
  simp only [PeriodicOrthocrossing.translatePolyline,
    List.head?_map, List.getLast?_map,
    oldEndpoints.1, oldEndpoints.2, Option.map_some]
  constructor
  · apply congrArg some
    rw [taggedEq]
    simp only [CNFIncidence.variableGauge]
    rw [incidenceVertexPositionAt_clause
      source placement tagged.1.clauseIndex clauseIndexLt]
    rw [incidenceVertexPositionAt_clause
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      tagged.1.clauseIndex gaugedClauseIndexLt]
    rw [clauseAt, gaugedClauseAt]
    exact (canonicalClausePosition_variableGauge
      placement gauge clause).symm
  · apply congrArg some
    rw [taggedEq]
    simp only [CNFIncidence.variableGauge]
    simp only [PeriodicGridDrawing.periodTranslation]
    rw [incidenceDrawing_gridSize
      source placement routes periodPositive]
    rw [incidenceDrawing_gridSize
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)]
    · simpa [PeriodicVariablePlacement.translation,
        CNFIncidence.edge, PeriodicCNF.incidenceEdge,
        variableGaugeCanonicalRouteShift] using
          canonicalLiteralEndpoint_variableGauge
            placement gauge clause.literals literal
    · simpa using periodPositive

/-- Canonical route transport preserves the complete incidence-graph
endpoint condition under an arbitrary variable gauge. -/
theorem incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph) :
    (incidenceDrawing
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).RoutesMatch
      (source.variableGauge gauge).erase.incidenceGraph := by
  intro taggedEdge taggedEdgeMember
  have metadataEdgeMember := taggedEdgeMember
  rw [← PeriodicCNF.incidencesWithMetadata_edges
      (source.variableGauge gauge).erase,
    List.zipIdx_map] at metadataEdgeMember
  rcases List.mem_map.mp metadataEdgeMember with
    ⟨gaugedTaggedIncidence, gaugedTaggedIncidenceMember,
      taggedEdgeEq⟩
  have gaugedTaggedIncidenceMember' :=
    gaugedTaggedIncidenceMember
  rw [erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.zipIdx_map] at gaugedTaggedIncidenceMember'
  rcases List.mem_map.mp gaugedTaggedIncidenceMember' with
    ⟨taggedIncidence, taggedIncidenceMember,
      gaugedTaggedIncidenceEq⟩
  subst gaugedTaggedIncidence
  have endpoints :=
    variableGaugeCanonicalIncidenceRoutes_endpoints_of_tagged
      source placement gauge routes periodPositive routesMatch
      taggedIncidenceMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed
      (source.variableGauge gauge).erase
  have edgeMember :
      (taggedIncidence.1.variableGauge gauge).edge ∈
        (source.variableGauge gauge).erase.incidenceGraph.edges :=
    List.fst_mem_of_mem_zipIdx
      (PeriodicCNF.tagged_incidence_edge_mem
        (source.variableGauge gauge).erase
        gaugedTaggedIncidenceMember)
  have endpointMembers :=
    graphWellFormed.2
      (taggedIncidence.1.variableGauge gauge).edge edgeMember
  have sourcePosition :=
    incidenceDrawing_vertexPosition_of_mem
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
      endpointMembers.1
  have targetPosition :=
    incidenceDrawing_vertexPosition_of_mem
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
      endpointMembers.2
  have routeLookup :=
    incidenceDrawing_edgeRoute_of_tagged
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
      gaugedTaggedIncidenceMember
  simp only [Prod.map, id_eq] at routeLookup
  rw [← taggedEdgeEq]
  simp only [Prod.map, id_eq]
  rw [routeLookup]
  constructor
  · rw [sourcePosition, CNFIncidence.edge_source]
    exact endpoints.1
  · rw [targetPosition, CNFIncidence.edge_target]
    exact endpoints.2

/-- Once the gauged finite vertex representatives are distinct and lie in
the open fundamental square, canonical route transport supplies every
remaining compatibility field automatically. -/
theorem incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_isCompatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph)
    (positionsNodup :
      (incidenceVertexPositions
        (source.variableGauge gauge)
        (placement.variableGauge gauge)).Nodup)
    (positionsInside :
      ∀ position ∈
          incidenceVertexPositions
            (source.variableGauge gauge)
            (placement.variableGauge gauge),
        (incidenceDrawing
          (source.variableGauge gauge)
          (placement.variableGauge gauge)
          (variableGaugeCanonicalIncidenceRoutes
            source placement gauge routes))
          |>.PositionInFundamentalSquare position) :
    (incidenceDrawing
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).IsCompatible
      (source.variableGauge gauge).erase.incidenceGraph := by
  refine
    ⟨PeriodicCNF.incidenceGraph_isWellFormed
        (source.variableGauge gauge).erase,
      incidenceVertexPositions_length
        (source.variableGauge gauge)
        (placement.variableGauge gauge),
      incidenceEdgeRoutes_length
        (source.variableGauge gauge)
        (variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes),
      positionsNodup, positionsInside, ?_⟩
  exact incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesMatch
    source placement gauge routes periodPositive routesMatch

/-- Translating each canonical route by its whole-period gauge shift
preserves orthogonality of the finite incidence drawing. -/
theorem incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (orthogonal :
      (incidenceDrawing source placement routes).IsOrthogonal) :
    (incidenceDrawing
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).IsOrthogonal := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
    at orthogonal ⊢
  intro gaugedRoute gaugedRouteMember
  change gaugedRoute ∈
    incidenceEdgeRoutes
      (source.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
    at gaugedRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.map_map] at gaugedRouteMember
  rcases List.mem_map.mp gaugedRouteMember with
    ⟨incidence, incidenceMember, gaugedRouteEq⟩
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember,
      incidenceEq⟩
  have sourceRouteMember :
      routes incidence.clauseIndex incidence.literalIndex ∈
        (incidenceDrawing source placement routes).edgeRoutes := by
    change routes incidence.clauseIndex incidence.literalIndex ∈
      incidenceEdgeRoutes source routes
    rw [incidenceEdgeRoutes_eq_metadata_map]
    exact List.mem_map.mpr
      ⟨incidence,
        List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩
  have sourceRouteOrthogonal :=
    orthogonal _ sourceRouteMember
  have transportedRouteEq :
      gaugedRoute =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (variableGaugeCanonicalRouteShift gauge clause))
          (routes incidence.clauseIndex incidence.literalIndex) := by
    rw [← gaugedRouteEq]
    change
      variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes
          incidence.clauseIndex incidence.literalIndex = _
    exact variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes clauseMember
  rw [transportedRouteEq]
  exact sourceRouteOrthogonal.translate _

/-- Coordinate-indexed relative route separation survives arbitrary
variable gauging and the corresponding canonical route translations. -/
theorem
    CoordinateRelativeIncidenceRoutesAvoidEachOther.variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (gauge : Variable → Cell)
    (separated :
      CoordinateRelativeIncidenceRoutesAvoidEachOther
        source placement routes) :
    CoordinateRelativeIncidenceRoutesAvoidEachOther
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes) := by
  intro firstGaugedClause firstClauseIndex firstClauseMember
    firstGaugedLiteral firstLiteralIndex firstLiteralMember
    secondGaugedClause secondClauseIndex secondClauseMember
    secondGaugedLiteral secondLiteralIndex secondLiteralMember
    relativeTranslate gaugedOccurrencesDifferent
  change
    (firstGaugedClause, firstClauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position,
          clause.literals.variableGauge gauge⟩).zipIdx
    at firstClauseMember
  change
    (secondGaugedClause, secondClauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position,
          clause.literals.variableGauge gauge⟩).zipIdx
    at secondClauseMember
  rw [List.zipIdx_map] at firstClauseMember secondClauseMember
  rcases List.mem_map.mp firstClauseMember with
    ⟨firstTaggedClause, firstTaggedClauseMember,
      firstGaugedClauseEq⟩
  rcases List.mem_map.mp secondClauseMember with
    ⟨secondTaggedClause, secondTaggedClauseMember,
      secondGaugedClauseEq⟩
  have firstClauseIndexEq :
      firstTaggedClause.2 = firstClauseIndex :=
    congrArg Prod.snd firstGaugedClauseEq
  have secondClauseIndexEq :
      secondTaggedClause.2 = secondClauseIndex :=
    congrArg Prod.snd secondGaugedClauseEq
  subst firstClauseIndex
  subst secondClauseIndex
  have firstGaugedClauseValueEq :
      firstGaugedClause =
        ⟨firstTaggedClause.1.position,
          firstTaggedClause.1.literals.variableGauge gauge⟩ :=
    (congrArg Prod.fst firstGaugedClauseEq).symm
  have secondGaugedClauseValueEq :
      secondGaugedClause =
        ⟨secondTaggedClause.1.position,
          secondTaggedClause.1.literals.variableGauge gauge⟩ :=
    (congrArg Prod.fst secondGaugedClauseEq).symm
  subst firstGaugedClause
  subst secondGaugedClause
  change
    (firstGaugedLiteral, firstLiteralIndex) ∈
      (firstTaggedClause.1.literals.map
        (PeriodicLiteral.variableGauge gauge)).zipIdx
    at firstLiteralMember
  change
    (secondGaugedLiteral, secondLiteralIndex) ∈
      (secondTaggedClause.1.literals.map
        (PeriodicLiteral.variableGauge gauge)).zipIdx
    at secondLiteralMember
  rw [List.zipIdx_map] at firstLiteralMember secondLiteralMember
  rcases List.mem_map.mp firstLiteralMember with
    ⟨firstTaggedLiteral, firstTaggedLiteralMember,
      firstGaugedLiteralEq⟩
  rcases List.mem_map.mp secondLiteralMember with
    ⟨secondTaggedLiteral, secondTaggedLiteralMember,
      secondGaugedLiteralEq⟩
  have firstLiteralIndexEq :
      firstTaggedLiteral.2 = firstLiteralIndex :=
    congrArg Prod.snd firstGaugedLiteralEq
  have secondLiteralIndexEq :
      secondTaggedLiteral.2 = secondLiteralIndex :=
    congrArg Prod.snd secondGaugedLiteralEq
  subst firstLiteralIndex
  subst secondLiteralIndex
  let firstShift :=
    variableGaugeCanonicalRouteShift
      gauge firstTaggedClause.1
  let secondShift :=
    variableGaugeCanonicalRouteShift
      gauge secondTaggedClause.1
  let adjustedTranslate :=
    Cell.sub
      (Cell.add relativeTranslate secondShift)
      firstShift
  have sourceOccurrencesDifferent :
      ((firstTaggedClause.2, firstTaggedLiteral.2), (0, 0)) ≠
        ((secondTaggedClause.2, secondTaggedLiteral.2),
          adjustedTranslate) := by
    intro equal
    have clauseIndicesEqual :
        firstTaggedClause.2 = secondTaggedClause.2 :=
      congrArg
        (fun occurrence : (Nat × Nat) × Cell =>
          occurrence.1.1) equal
    have literalIndicesEqual :
        firstTaggedLiteral.2 = secondTaggedLiteral.2 :=
      congrArg
        (fun occurrence : (Nat × Nat) × Cell =>
          occurrence.1.2) equal
    have adjustedEqual : (0, 0) = adjustedTranslate :=
      congrArg
        (fun occurrence : (Nat × Nat) × Cell =>
          occurrence.2) equal
    have sourceClausesEqual :
        firstTaggedClause.1 = secondTaggedClause.1 := by
      have firstLookup :=
        (List.mem_zipIdx_iff_getElem?).mp
          firstTaggedClauseMember
      have secondLookup :=
        (List.mem_zipIdx_iff_getElem?).mp
          secondTaggedClauseMember
      rw [clauseIndicesEqual, secondLookup] at firstLookup
      exact Option.some.inj firstLookup.symm
    have shiftsEqual : firstShift = secondShift := by
      simp [firstShift, secondShift, sourceClausesEqual]
    have relativeEqual : relativeTranslate = (0, 0) := by
      rcases relativeTranslate with ⟨relativeX, relativeY⟩
      rcases firstShift with ⟨firstShiftX, firstShiftY⟩
      rcases secondShift with ⟨secondShiftX, secondShiftY⟩
      simp [adjustedTranslate, Cell.add, Cell.sub]
        at adjustedEqual shiftsEqual
      apply Prod.ext <;> omega
    apply gaugedOccurrencesDifferent
    exact Prod.ext
      (Prod.ext clauseIndicesEqual literalIndicesEqual)
      relativeEqual.symm
  have sourceAvoids := separated
    firstTaggedClause.1 firstTaggedClause.2
      firstTaggedClauseMember
    firstTaggedLiteral.1 firstTaggedLiteral.2
      firstTaggedLiteralMember
    secondTaggedClause.1 secondTaggedClause.2
      secondTaggedClauseMember
    secondTaggedLiteral.1 secondTaggedLiteral.2
      secondTaggedLiteralMember
    adjustedTranslate sourceOccurrencesDifferent
  have firstRouteEq :=
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes firstTaggedClauseMember
      (literalIndex := firstTaggedLiteral.2)
  have secondRouteEq :=
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes secondTaggedClauseMember
      (literalIndex := secondTaggedLiteral.2)
  rw [firstRouteEq, secondRouteEq]
  have translatedAvoids :=
    sourceAvoids.translate (placement.translation firstShift)
  have secondTranslationEq :
      PeriodicOrthocrossing.translatePolyline
          (placement.translation firstShift)
          ((routes secondTaggedClause.2
              secondTaggedLiteral.2).map
            (Cell.add
              (placement.translation adjustedTranslate))) =
        (PeriodicOrthocrossing.translatePolyline
          (placement.translation secondShift)
          (routes secondTaggedClause.2
            secondTaggedLiteral.2)).map
          (Cell.add
            ((placement.variableGauge gauge).translation
              relativeTranslate)) := by
    unfold PeriodicOrthocrossing.translatePolyline
    simp only [List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    rcases point with ⟨pointX, pointY⟩
    rcases firstShift with ⟨firstShiftX, firstShiftY⟩
    rcases secondShift with ⟨secondShiftX, secondShiftY⟩
    rcases relativeTranslate with ⟨relativeX, relativeY⟩
    simp [adjustedTranslate,
      PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale,
      PeriodicVariablePlacement.variableGauge]
    constructor <;> ring
  rw [secondTranslationEq] at translatedAvoids
  exact translatedAvoids

/-- Flat-indexed relative route separation survives arbitrary variable
gauging and canonical route representative transport. -/
theorem
    RelativeIncidenceRoutesAvoidEachOther.variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (gauge : Variable → Cell)
    (separated :
      RelativeIncidenceRoutesAvoidEachOther
        source placement routes) :
    RelativeIncidenceRoutesAvoidEachOther
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes) :=
  separated.coordinate
    |>.variableGaugeCanonicalIncidenceRoutes gauge
    |>.relative

/-- Translating each canonical route by its whole-period gauge shift
preserves route-local simplicity throughout the incidence drawing. -/
theorem routesSimple_variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (simple :
      ∀ route ∈ (incidenceDrawing source placement routes).edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈
        (incidenceDrawing
          (source.variableGauge gauge)
          (placement.variableGauge gauge)
          (variableGaugeCanonicalIncidenceRoutes
            source placement gauge routes)).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro gaugedRoute gaugedRouteMember
  change gaugedRoute ∈
    incidenceEdgeRoutes
      (source.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)
    at gaugedRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.map_map] at gaugedRouteMember
  rcases List.mem_map.mp gaugedRouteMember with
    ⟨incidence, incidenceMember, gaugedRouteEq⟩
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, _literal, clauseMember, _literalMember, _incidenceEq⟩
  have sourceRouteMember :
      routes incidence.clauseIndex incidence.literalIndex ∈
        (incidenceDrawing source placement routes).edgeRoutes := by
    change routes incidence.clauseIndex incidence.literalIndex ∈
      incidenceEdgeRoutes source routes
    rw [incidenceEdgeRoutes_eq_metadata_map]
    exact List.mem_map.mpr
      ⟨incidence, List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩
  have transportedRouteEq :
      gaugedRoute =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (variableGaugeCanonicalRouteShift gauge clause))
          (routes incidence.clauseIndex incidence.literalIndex) := by
    rw [← gaugedRouteEq]
    change
      variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes
          incidence.clauseIndex incidence.literalIndex = _
    exact variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes clauseMember
  rw [transportedRouteEq]
  exact routeIsSimple_translate
    (simple _ sourceRouteMember) _

end PositionedPeriodicCNF
end LeanTrominoes
