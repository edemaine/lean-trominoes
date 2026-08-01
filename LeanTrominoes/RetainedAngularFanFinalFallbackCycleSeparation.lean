import LeanTrominoes.RetainedAngularFanFinalCoordinatedFallbackOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOtherCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalOccurrenceSuffixSeparation

/-!
# Final fallback occurrences avoid every implication cycle

The different-center case follows from disjoint source neighborhoods.  When
the centers agree, uniqueness of periodic representatives identifies the
metadata atom and forces the occurrence's relative offset to vanish.  The
selected flattened route is then exactly the already-certified matching
cycle lift.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Equality between a genuine source occurrence center and another
occurring source center identifies the atom and says that the occurrence is
in the canonical clause translate. -/
theorem
    retainedFinalCanonicalLiteralPosition_eq_sourcePosition_imp
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        (finalCoordinatedPlacement formula).position
          targetAtom) :
    literal.atom = targetAtom ∧
      incidenceRelativeOffset
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal =
        (0, 0) := by
  let placement := finalCoordinatedPlacement formula
  let targetLiteral :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable) :=
    { atom := targetAtom
      offset := PeriodicCNF.clauseAnchor clause.literals
      value := true }
  have targetCanonical :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause targetLiteral =
        placement.position targetAtom := by
    simp [PositionedPeriodicCNF.canonicalLiteralPosition,
      targetLiteral, PeriodicVariablePlacement.translation,
      Cell.sub, Cell.add, Cell.scale]
  have literalStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula literal.atom
  have targetStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula targetAtom
  have literalBounds :
      0 ≤ (placement.position literal.atom).1 ∧
        (placement.position literal.atom).1 < placement.period ∧
        0 ≤ (placement.position literal.atom).2 ∧
        (placement.position literal.atom).2 < placement.period := by
    simpa [placement, finalCoordinatedPlacement] using
      And.intro literalStrictBounds.1.le
        (And.intro literalStrictBounds.2.1
          (And.intro literalStrictBounds.2.2.1.le
            literalStrictBounds.2.2.2))
  have targetBounds :
      0 ≤ (placement.position targetLiteral.atom).1 ∧
        (placement.position targetLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position targetLiteral.atom).2 ∧
        (placement.position targetLiteral.atom).2 < placement.period := by
    simpa [placement, targetLiteral, finalCoordinatedPlacement] using
      And.intro targetStrictBounds.1.le
        (And.intro targetStrictBounds.2.1
          (And.intro targetStrictBounds.2.2.1.le
            targetStrictBounds.2.2.2))
  have positionAndOffsetEqual :=
    PositionedPeriodicCNF.canonicalLiteralPosition_eq_sameClause_imp
      placement
      (by
        simpa [placement, finalCoordinatedPlacement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement]
          using drawingPeriodicPlanarSATPlacement_period_pos formula)
      clause literal targetLiteral
      literalBounds targetBounds
      (by simpa [placement, targetCanonical] using centersEqual)
  have literalTagged :
      (literal, clauseIndex, literalIndex) ∈
        taggedLiterals (finalCoordinatedSource formula).erase :=
    taggedLiteral_mem_of_positioned_members
      (finalCoordinatedSource formula)
      clauseMember literalMember
  have literalAtomMember :
      literal.atom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase := by
    simpa only [PositionedPeriodicCNF.erase_scale] using
      sourceVariables_mem
        (finalCoordinatedSource formula).erase literalTagged
  have atomsEqual :
      literal.atom = targetAtom := by
    apply
      retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        literalAtomMember targetAtomMember
    simpa [PeriodicVariablePlacement.scale] using
      congrArg
        (Cell.scale retainedAngularFanSourceClearanceFactor)
        positionAndOffsetEqual.1
  constructor
  · exact atomsEqual
  · simp [incidenceRelativeOffset,
      PositionedPeriodicClause.scale_literals,
      positionAndOffsetEqual.2, targetLiteral, Cell.sub]

/-- A genuine local Figure 7 clause index is within the nine-clause cycle
presentation. -/
theorem positionedCycleClause_localIndex_lt
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {localClauseIndex : Nat}
    (clauseMember :
      (clause, localClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx) :
    localClauseIndex < presentedCycleVertices.length := by
  have indexLt :=
    List.snd_lt_of_mem_zipIdx clauseMember
  simpa [PeriodicEightOccurrenceSplitPositioned.cycleClausesFor_eq_cycleFormula,
    cycleFormula] using indexLt

/-- Every literal index of a genuine local Figure 7 implication clause is
one of its two sides. -/
theorem positionedCycleClause_literalIndex_lt_two
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {localClauseIndex : Nat}
    (clauseMember :
      (clause, localClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    literalIndex < 2 := by
  rw [PeriodicEightOccurrenceSplitPositioned.cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  have clauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  have embeddedClauseMember :
      taggedClause.1 ∈ cycleFormula :=
    List.fst_mem_of_mem_zipIdx taggedClauseMember
  rw [cycleFormula] at embeddedClauseMember
  rcases List.mem_map.mp embeddedClauseMember with
    ⟨vertex, _vertexMember, embeddedClauseEqual⟩
  subst clause
  rw [← embeddedClauseEqual] at literalMember
  have literalIndexLt :=
    List.snd_lt_of_mem_zipIdx literalMember
  simpa [positionedLocalCycleClause, periodicCycleClause,
    OccurrenceSplitRing.cycleClause] using literalIndexLt

/-- If a flattened cycle entry has the same source center as an occurrence,
its route is definitionally the matching translated lift: periodic
uniqueness has forced both the owning atom and translation to agree. -/
theorem
    retainedFinalScaledAllCycleRoute_eq_matchingCycleLift_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        (finalCoordinatedPlacement formula).position
          metadata.atom) :
    scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex) =
      retainedFinalMatchingCycleLift
        formula clause literal
        metadata.localClauseIndex cycleLiteralIndex := by
  have metadataAtomMember :
      metadata.atom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase :=
    allCycleClauseMetadata_lookup_atom_mem
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadataLookup
  have identified :=
    retainedFinalCanonicalLiteralPosition_eq_sourcePosition_imp
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadata.atom metadataAtomMember centersEqual
  unfold retainedFinalMatchingCycleLift
  unfold allCycleRoutes
  rw [metadataLookup, identified.1, identified.2]
  change
    scalePolyline retainedTerminalFanRoutingRefinement
        (positionedCycleRoutes
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          metadata.atom metadata.localClauseIndex
          cycleLiteralIndex) =
      scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline (0, 0)
          (positionedCycleRoutes
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            metadata.atom metadata.localClauseIndex
            cycleLiteralIndex))
  rw [translatePolyline_zero]

/-- Every failed-choice occurrence in the public coordinated source family
avoids every genuine flattened implication-cycle route. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_allCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      localClauseMember⟩
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        (finalCoordinatedPlacement formula).position
          metadata.atom
  · have routeEqual :=
      retainedFinalScaledAllCycleRoute_eq_matchingCycleLift_of_center_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        metadataLookup cycleLiteralIndex centersEqual
    have localClauseIndexLt :
        metadata.localClauseIndex <
          presentedCycleVertices.length :=
      positionedCycleClause_localIndex_lt
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor)
        metadata.atom localClauseMember
    have localLiteralMember :
        (cycleLiteral, cycleLiteralIndex) ∈
          metadata.clause.literals.zipIdx := by
      simpa [metadataClauseEqual] using cycleLiteralMember
    have cycleLiteralIndexLt :
        cycleLiteralIndex < 2 :=
      positionedCycleClause_literalIndex_lt_two
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor)
        metadata.atom localClauseMember
        localLiteralMember
    have avoids :=
      retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_matchingCycleLift
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        metadata.localClauseIndex cycleLiteralIndex
        localClauseIndexLt cycleLiteralIndexLt
    rw [routeEqual]
    exact avoids
  · exact
      (retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        metadataLookup cycleLiteralIndex centersEqual).toRoutesAvoidEachOther

end PeriodicOrthocrossing
end LeanTrominoes
