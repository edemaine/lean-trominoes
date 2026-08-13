/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularBoundaryRoutes
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitRoutes

/-!
# Complete angular-spliced occurrence-splitting routes

Given boundary-reaching routes for the copied source incidences, this file
assembles the complete route family for positioned fixed-eight occurrence
splitting.  Copied clauses join those prefixes to certified angular fan
spokes; appended implication clauses retain their certified Figure 7 cycle
routes.

The construction is total on presentation indices, while its endpoint and
orthogonality theorems only need the genuine incidence memberships exposed
by the final formula.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Total copied-source route lookup obtained from an angular boundary
certificate.  Invalid presentation indices receive the harmless empty
route. -/
def angularSplicedOccurrenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {order : OccurrenceOrder source.erase}
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            angularSplicedOccurrenceRoute boundary
              clause literal clauseIndex literalIndex

/-- Genuine source indices reduce the total lookup to the explicit angular
splice for their source clause and literal. -/
theorem angularSplicedOccurrenceRoutes_of_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {order : OccurrenceOrder source.erase}
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    angularSplicedOccurrenceRoutes boundary
        clauseIndex literalIndex =
      angularSplicedOccurrenceRoute boundary
        clause literal clauseIndex literalIndex := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [angularSplicedOccurrenceRoutes,
    clauseLookup, literalLookup]

/-- Complete route family: angular-spliced copied clauses followed by the
already certified local implication-cycle routes. -/
def angularSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    if clauseIndex <
        (occurrenceClauses source
          (occurrencePortsOfAngularOrder
            source.erase order)).length
    then
      angularSplicedOccurrenceRoutes boundary
        clauseIndex literalIndex
    else
      allCycleRoutes source sourcePlacement
        (clauseIndex -
          (occurrenceClauses source
            (occurrencePortsOfAngularOrder
              source.erase order)).length)
        literalIndex

/-- Before the append boundary, the complete family is the angular-spliced
copied-source family. -/
theorem angularSplicedIncidenceRoutes_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    (clauseIndex literalIndex : Nat)
    (occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source
          (occurrencePortsOfAngularOrder
            source.erase order)).length) :
    angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        clauseIndex literalIndex =
      angularSplicedOccurrenceRoutes boundary
        clauseIndex literalIndex := by
  simp [angularSplicedIncidenceRoutes,
    occurrenceIndex]

/-- In the appended suffix, the complete family is exactly the flattened
certified implication-cycle family. -/
theorem angularSplicedIncidenceRoutes_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    (cycleIndex literalIndex : Nat) :
    angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        ((occurrenceClauses source
            (occurrencePortsOfAngularOrder
              source.erase order)).length +
          cycleIndex)
        literalIndex =
      allCycleRoutes source sourcePlacement
        cycleIndex literalIndex := by
  simp [angularSplicedIncidenceRoutes]

/-- A final-formula clause before the append boundary belongs to the copied
source prefix at the same index. -/
theorem occurrenceClauseMember_of_formula_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement
          (occurrencePortsOfAngularOrder
            source.erase order)).clauses.zipIdx)
    (occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source
          (occurrencePortsOfAngularOrder
            source.erase order)).length) :
    (clause, clauseIndex) ∈
      (occurrenceClauses source
        (occurrencePortsOfAngularOrder
          source.erase order)).zipIdx := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  change
    (occurrenceClauses source
        (occurrencePortsOfAngularOrder
          source.erase order) ++
      allCycleClauses source sourcePlacement)[clauseIndex]? =
        some clause
    at clauseLookup
  rw [List.getElem?_append_left occurrenceIndex]
    at clauseLookup
  exact List.mem_zipIdx_iff_getElem?.mpr clauseLookup

/-- Every genuine complete route meets the final copied or implication
clause and literal at their canonical periodic endpoints. -/
theorem angularSplicedIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement
          (occurrencePortsOfAngularOrder
            source.erase order)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) clause) ∧
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement sourcePlacement) clause literal) := by
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source sourcePlacement order
        clauseMember occurrenceIndex
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, clauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        clause =
          occurrenceClause occurrencePorts
            clauseIndex metadata.sourceClause := by
      calc
        clause = metadata.clause :=
          metadataClauseEqual.symm
        _ =
            occurrenceClause occurrencePorts
              metadata.clauseIndex metadata.sourceClause :=
          metadataClauseDefinition
        _ =
            occurrenceClause occurrencePorts
              clauseIndex metadata.sourceClause := by
          rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual literalMember with
      ⟨sourceLiteral, sourceLiteralMember,
        copiedLiteralEqual⟩
    have explicitValid :=
      angularSplicedOccurrenceRoute_valid
        boundary sourceClauseMemberAt sourceLiteralMember
    rw [angularSplicedIncidenceRoutes_occurrence
      source sourcePlacement order boundary
      clauseIndex literalIndex occurrenceIndex,
      angularSplicedOccurrenceRoutes_of_members
        boundary sourceClauseMemberAt sourceLiteralMember]
    simpa [occurrencePorts, copiedClauseEqual,
      copiedLiteralEqual] using
        And.intro explicitValid.1 explicitValid.2.1
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source sourcePlacement occurrencePorts
        clauseMember occurrenceIndex
    have cycleEndpoints :=
      allCycleRoutes_physicalRoutesMatch
        source sourcePlacement
        clause
        (clauseIndex -
          (occurrenceClauses
            source occurrencePorts).length)
        cycleClauseMember literal literalIndex
        literalMember
    have clauseIndexDecomposition :
        clauseIndex =
          (occurrenceClauses
            source occurrencePorts).length +
            (clauseIndex -
              (occurrenceClauses
                source occurrencePorts).length) := by
      omega
    rw [clauseIndexDecomposition,
      angularSplicedIncidenceRoutes_cycle]
    have anchorZero :=
      allCycleClauses_clauseAnchor_eq_zero
        source sourcePlacement cycleClauseMember
    have offsetZero :=
      allCycleClauses_literal_offset_eq_zero
        source sourcePlacement cycleClauseMember
        literalMember
    constructor
    · simpa [PositionedPeriodicCNF.canonicalClausePosition,
        anchorZero,
        PeriodicVariablePlacement.translation,
        Cell.sub, Cell.scale] using cycleEndpoints.1
    · simpa [PositionedPeriodicCNF.canonicalLiteralPosition,
        PeriodicVariablePlacement.literalPosition,
        anchorZero, offsetZero,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale] using
          cycleEndpoints.2

/-- Every genuine route in the complete family is an orthogonal polyline. -/
theorem angularSplicedIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement
          (occurrencePortsOfAngularOrder
            source.erase order)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        clauseIndex literalIndex) := by
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source sourcePlacement order
        clauseMember occurrenceIndex
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, clauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        clause =
          occurrenceClause occurrencePorts
            clauseIndex metadata.sourceClause := by
      calc
        clause = metadata.clause :=
          metadataClauseEqual.symm
        _ =
            occurrenceClause occurrencePorts
              metadata.clauseIndex metadata.sourceClause :=
          metadataClauseDefinition
        _ =
            occurrenceClause occurrencePorts
              clauseIndex metadata.sourceClause := by
          rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual literalMember with
      ⟨sourceLiteral, sourceLiteralMember,
        _copiedLiteralEqual⟩
    rw [angularSplicedIncidenceRoutes_occurrence
      source sourcePlacement order boundary
      clauseIndex literalIndex occurrenceIndex,
      angularSplicedOccurrenceRoutes_of_members
        boundary sourceClauseMemberAt sourceLiteralMember]
    exact
      (angularSplicedOccurrenceRoute_valid
        boundary sourceClauseMemberAt
          sourceLiteralMember).2.2
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source sourcePlacement occurrencePorts
        clauseMember occurrenceIndex
    have clauseIndexDecomposition :
        clauseIndex =
          (occurrenceClauses
            source occurrencePorts).length +
            (clauseIndex -
              (occurrenceClauses
                source occurrencePorts).length) := by
      omega
    rw [clauseIndexDecomposition,
      angularSplicedIncidenceRoutes_cycle]
    exact allCycleRoutes_orthogonal
      source sourcePlacement cycleClauseMember
      literalMember

/-- Metadata-rich incidences retrieve the canonical endpoints of the fully
angular-spliced route family. -/
theorem angularSplicedIncidenceRoutes_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    {tagged :
      CNFIncidence
        (ThreeOccurrenceVariable Variable) × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata
          (formula source sourcePlacement
            (occurrencePortsOfAngularOrder
              source.erase order)).erase).zipIdx) :
    (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        tagged.1.clauseIndex
        tagged.1.literalIndex).head? =
        some
          (PositionedPeriodicCNF.incidenceVertexPositionAt
            (formula source sourcePlacement
              (occurrencePortsOfAngularOrder
                source.erase order))
            (placement sourcePlacement)
            (.clause tagged.1.clauseIndex)) ∧
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        tagged.1.clauseIndex
        tagged.1.literalIndex).getLast? =
        some
          (Cell.add
            ((placement sourcePlacement).position
              tagged.1.literal.atom)
            ((placement sourcePlacement).translation
              tagged.1.edge.offset)) := by
  let finalFormula :=
    formula source sourcePlacement
      (occurrencePortsOfAngularOrder
        source.erase order)
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      finalFormula taggedMember with
    ⟨clause, literal, clauseMember,
      literalMember, taggedEqual⟩
  have clauseIndexLt :
      tagged.1.clauseIndex <
        finalFormula.clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have clauseLookup :
      finalFormula.clauses[
        tagged.1.clauseIndex] = clause :=
    (List.mem_zipIdx' clauseMember).2.symm
  have endpoints :=
    angularSplicedIncidenceRoutes_endpoints
      source sourcePlacement order boundary
      clauseMember literalMember
  rw [taggedEqual]
  constructor
  · simpa [finalFormula,
      PositionedPeriodicCNF.incidenceVertexPositionAt,
      List.getElem?_eq_getElem clauseIndexLt,
      clauseLookup] using endpoints.1
  · simpa [PositionedPeriodicCNF.canonicalLiteralPosition,
      CNFIncidence.edge,
      PeriodicCNF.incidenceEdge] using endpoints.2

/-- The complete angular-spliced drawing satisfies the periodic incidence
graph's full endpoint condition. -/
theorem angularSplicedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    (sourcePeriodPositive :
      0 < sourcePlacement.period) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder
          source.erase order))
      (placement sourcePlacement)
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)).RoutesMatch
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder
          source.erase order)).erase.incidenceGraph := by
  let finalFormula :=
    formula source sourcePlacement
      (occurrencePortsOfAngularOrder
        source.erase order)
  intro taggedEdge taggedEdgeMember
  have metadataEdgeMember := taggedEdgeMember
  rw [← PeriodicCNF.incidencesWithMetadata_edges
      finalFormula.erase,
    List.zipIdx_map] at metadataEdgeMember
  rcases List.mem_map.mp metadataEdgeMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedIncidenceEqual⟩
  have endpoints :=
    angularSplicedIncidenceRoutes_endpoints_of_tagged
      source sourcePlacement order boundary
      taggedIncidenceMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed
      finalFormula.erase
  have edgeMember :
      taggedIncidence.1.edge ∈
        finalFormula.erase.incidenceGraph.edges :=
    List.fst_mem_of_mem_zipIdx
      (PeriodicCNF.tagged_incidence_edge_mem
        finalFormula.erase taggedIncidenceMember)
  have endpointMembers :=
    graphWellFormed.2 taggedIncidence.1.edge edgeMember
  have sourcePosition :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      finalFormula
      (placement sourcePlacement)
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)
      endpointMembers.1
  have targetPosition :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      finalFormula
      (placement sourcePlacement)
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)
      endpointMembers.2
  have routeLookup :=
    PositionedPeriodicCNF.incidenceDrawing_edgeRoute_of_tagged
      finalFormula
      (placement sourcePlacement)
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)
      taggedIncidenceMember
  rw [← taggedIncidenceEqual]
  simp only [Prod.map, id_eq]
  rw [routeLookup]
  constructor
  · rw [sourcePosition, CNFIncidence.edge_source]
    exact endpoints.1
  · rw [targetPosition, CNFIncidence.edge_target]
    simp only [PositionedPeriodicCNF.incidenceVertexPositionAt,
      PeriodicGridDrawing.periodTranslation]
    rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
      finalFormula
      (placement sourcePlacement)
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)
      (placement_period_pos
        sourcePlacement sourcePeriodPositive)]
    simpa [PeriodicVariablePlacement.translation] using
      endpoints.2

/-- The complete angular-spliced incidence drawing is orthogonal. -/
theorem angularSplicedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder
          source.erase order))
      (placement sourcePlacement)
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)).IsOrthogonal := by
  let finalFormula :=
    formula source sourcePlacement
      (occurrencePortsOfAngularOrder
        source.erase order)
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  intro route routeMember
  change route ∈
    PositionedPeriodicCNF.incidenceEdgeRoutes
      finalFormula
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary)
    at routeMember
  rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map]
    at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEqual⟩
  subst route
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata
          finalFormula.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      finalFormula taggedMember with
    ⟨clause, literal, clauseMember,
      literalMember, _taggedEqual⟩
  exact angularSplicedIncidenceRoutes_orthogonal
    source sourcePlacement order boundary
    clauseMember literalMember

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
