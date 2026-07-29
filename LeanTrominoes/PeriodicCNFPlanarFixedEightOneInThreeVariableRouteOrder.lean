import LeanTrominoes.PeriodicEightOccurrenceSplitVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeRoutes
import LeanTrominoes.PeriodicOneInThreePositionedRouteTerminalDirectionTransport

/-!
# Variable route order through fixed-eight Figure 9

The fixed-eight angular-spliced source routes have already been proved to
follow syntactic occurrence order clockwise.  This file supplies their
nondegeneracy certificate and instantiates the generic Figure 9
terminal-direction transport, carrying that order to the raw exact-one
formula.
-/

namespace LeanTrominoes

/-- A witnessed first exit is exactly the nondegeneracy needed by terminal
direction transport. -/
private theorem length_ge_two_of_tail_head?
    {α : Type*} {route : List α} {exit : α}
    (tailHead : route.tail.head? = some exit) :
    2 ≤ route.length := by
  cases route with
  | nil =>
      simp at tailHead
  | cons first rest =>
      cases rest with
      | nil =>
          simp at tailHead
      | cons second tail =>
          simp

namespace PositionedPeriodicCNF

/-- The route-order proposition is independent of the lawful equality
decision procedure used to filter syntactic occurrences. -/
theorem variableRoutesInOccurrenceOrder_of_decidableEq
    {Variable : Type*}
    (firstEq secondEq : DecidableEq Variable)
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (ordered :
      @VariableRoutesInOccurrenceOrder
        Variable firstEq source routes) :
    @VariableRoutesInOccurrenceOrder
      Variable secondEq source routes := by
  intro atom first second third
    firstLookup secondLookup thirdLookup
  change
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable secondEq source.erase atom .first =
      some first at firstLookup
  change
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable secondEq source.erase atom .second =
      some second at secondLookup
  change
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable secondEq source.erase atom .third =
      some third at thirdLookup
  apply ordered atom first second third
  · change
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          Variable firstEq source.erase atom .first =
        some first
    rw [
      PeriodicEightOccurrenceSplitPositioned.occurrenceAt_eq_of_decidableEq
        firstEq secondEq source.erase atom .first]
    exact firstLookup
  · change
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          Variable firstEq source.erase atom .second =
        some second
    rw [
      PeriodicEightOccurrenceSplitPositioned.occurrenceAt_eq_of_decidableEq
        firstEq secondEq source.erase atom .second]
    exact secondLookup
  · change
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          Variable firstEq source.erase atom .third =
        some third
    rw [
      PeriodicEightOccurrenceSplitPositioned.occurrenceAt_eq_of_decidableEq
        firstEq secondEq source.erase atom .third]
    exact thirdLookup

end PositionedPeriodicCNF

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT

/-- Joining any nonempty prefix to a suffix with a genuine edge leaves at
least one edge in the completed route. -/
private theorem joinAtEndpoint_length_ge_two
    {α : Type*} {first second : List α} {point : α}
    (firstHead : first.head? = some point)
    (secondLength : 2 ≤ second.length) :
    2 ≤ (joinAtEndpoint first second).length := by
  cases first with
  | nil =>
      simp at firstHead
  | cons firstPoint firstTail =>
      cases second with
      | nil =>
          simp at secondLength
      | cons secondPoint secondTail =>
          cases secondTail with
          | nil =>
              simp at secondLength
          | cons secondNext secondRest =>
              simp [joinAtEndpoint]
              omega

/-- Every genuine translated Figure 7 implication route contains an edge. -/
theorem positionedCycleRoutes_length_ge_two
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor
          sourcePlacement atom).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    2 ≤
      (positionedCycleRoutes sourcePlacement atom
        clauseIndex literalIndex).length := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have positionedClauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clauseIndex
  subst clause
  change
    (literal, literalIndex) ∈
      (taggedClause.1.literals.map fun sourceLiteral =>
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom sourceLiteral.1,
          (0, 0), sourceLiteral.2⟩).zipIdx
    at literalMember
  rw [List.zipIdx_map] at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨taggedLiteral, taggedLiteralMember,
      taggedLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd taggedLiteralEqual
  subst literalIndex
  rcases cycleDrawing.exists_route_tail_head?_of_valid
      cycleDrawing_isValid taggedClauseMember
      taggedLiteralMember with
    ⟨exit, localTailHead⟩
  have localLength :
      2 ≤
        (cycleDrawing.routes
          taggedClause.2 taggedLiteral.2).length :=
    length_ge_two_of_tail_head? localTailHead
  simpa [positionedCycleRoutes,
    translatedCycleDrawing,
    EmbeddedCNFIncidenceDrawing.translate] using localLength

/-- Every genuine flattened implication-cycle route contains an edge. -/
theorem allCycleRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    2 ≤
      (allCycleRoutes source sourcePlacement
        cycleIndex literalIndex).length := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      localClauseMember⟩
  have localLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClauseEqual] using literalMember
  simpa [allCycleRoutes, metadataLookup] using
    positionedCycleRoutes_length_ge_two
      sourcePlacement metadata.atom localClauseMember
      localLiteralMember

/-- Every genuine angular-spliced fixed-eight route contains a final edge. -/
theorem angularSplicedIncidenceRoutes_length_ge_two
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
    2 ≤
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary
        clauseIndex literalIndex).length := by
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source sourcePlacement order
        clauseMember occurrenceIndex
    rcases occurrenceMetadata_of_members
        source occurrencePorts copiedClauseMember
        literalMember with
      ⟨metadata, sourceLiteral,
        metadataClauseEqual, metadataIndex,
        sourceClauseMember, sourceLiteralMember,
        _copiedLiteralEqual⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, clauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    rw [angularSplicedIncidenceRoutes_occurrence
      source sourcePlacement order boundary
      clauseIndex literalIndex occurrenceIndex]
    rw [angularSplicedOccurrenceRoutes_of_members
      boundary sourceClauseMemberAt sourceLiteralMember]
    unfold angularSplicedOccurrenceRoute
    apply joinAtEndpoint_length_ge_two
      (boundary.endpoints
        metadata.sourceClause clauseIndex
        sourceClauseMemberAt
        sourceLiteral literalIndex
        sourceLiteralMember).1
    exact angularOccurrenceSuffix_length_ge_two
      sourcePlacement order metadata.sourceClause
      sourceLiteral clauseIndex literalIndex
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source sourcePlacement occurrencePorts
        clauseMember occurrenceIndex
    have clauseIndexDecomposition :
        clauseIndex =
          (occurrenceClauses source occurrencePorts).length +
            (clauseIndex -
              (occurrenceClauses
                source occurrencePorts).length) := by
      omega
    rw [clauseIndexDecomposition,
      angularSplicedIncidenceRoutes_cycle]
    exact allCycleRoutes_length_ge_two
      source sourcePlacement cycleClauseMember literalMember

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 800000

/-- The concrete fixed-eight source routes satisfy the variable-side order
invariant required by the planar 3DM ribbon construction. -/
theorem
    drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input) := by
  apply
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
  apply fitsEightSlots_of_occurrencesAtMostEight
  rw [
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight_of_source
      sourceLocal sourceWidth sourceOccurrences

/-- Every genuine concrete fixed-eight source route contains a final edge. -/
theorem
    drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingAngularEightOccurrenceSplitPositionedFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input clauseIndex literalIndex).length := by
  simpa [drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes,
    drawingAngularEightOccurrenceSplitPositionedFormula,
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes]
    using
    PeriodicEightOccurrenceSplitPositioned.angularSplicedIncidenceRoutes_length_ge_two
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input)
      (wrappedDrawingPeriodicPlanarSATPlacement input)
      (drawingOrderedAngularOccurrenceOrder input)
      (PeriodicEightOccurrenceSplitPositioned.canonicalAngularBoundaryRoutes
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input)
        (wrappedDrawingPeriodicPlanarSATPlacement input)
        (drawingOrderedAngularOccurrenceOrder input))
      clauseMember literalMember

/-- The raw Figure 9 route family preserves terminal direction on every
inherited fixed-eight incidence. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_preservesOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PeriodicOneInThreePositioned.PreservesOriginalRouteTerminalDirections
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes input)
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences) := by
  simpa
    [drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes]
    using
      PeriodicOneInThreePositioned.preservesOriginalRouteTerminalDirections_splicedRoutes
        (drawingAngularEightOccurrenceSplitPositionedFormula input)
        (drawingAngularEightOccurrenceSplitPlacement input)
        (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
          input sourceWidth)
        (drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
          input sourceLocal sourceWidth sourceOccurrences)
        (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes input)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_endpoints
            input sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_orthogonal
            input sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_length_ge_two
            input sourceClauseMember sourceLiteralMember)

end PeriodicOrthocrossing
end LeanTrominoes
