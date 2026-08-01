import LeanTrominoes.RetainedAngularFanFinalFallbackCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Final direct occurrences avoid cycles at other source centers

The direct-source atlas replaces a two-point source incidence by a
coordinated outer fan.  A finite certificate bounds every such replacement
inside the radius-288 expansion of the fully refined source segment.  This
lets the retained source drawing's vertex/segment separation clear every
cycle centered at a different source atom.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every finite direct-source atlas route stays within the radius-288
expansion of its fully refined two-point local source segment. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈ retainedDirectSourceFanCompleteRouteAt kind index slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  native_decide

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A successful direct occurrence avoids a flattened cycle route at the
same canonical source center. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
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
        cycleClause.literals.zipIdx)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          (finalCoordinatedPlacement formula).position
            metadata.atom) :
    RoutesAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
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
  have routeEqual :=
    retainedFinalScaledAllCycleRoute_eq_matchingCycleLift_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadataLookup cycleLiteralIndex
      (centersEqual metadata metadataLookup)
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
      metadata.atom localClauseMember localLiteralMember
  have avoids :=
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_matchingCycleLift
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadata.localClauseIndex cycleLiteralIndex
      localClauseIndexLt cycleLiteralIndexLt
  dsimp only at avoids
  rw [routeEqual]
  exact avoids

/-- The public coordinated route selected by a successful direct choice
inherits the same-center cycle certificate. -/
theorem
    retainedFinalCoordinatedDirectSourceRoute_avoids_allCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
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
        cycleClause.literals.zipIdx)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          (finalCoordinatedPlacement formula).position
            metadata.atom) :
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
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? =
        some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup clauseLookup literalLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      cycleClauseMember cycleLiteralMember centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
