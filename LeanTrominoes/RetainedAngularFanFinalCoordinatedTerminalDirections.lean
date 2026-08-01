import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.PeriodicEightOccurrenceSplitRouteTerminalDirections

/-!
# Terminal directions of final coordinated occurrence routes

Every copied-source route variant ends by reusing the same scaled Figure 7
occurrence suffix.  This module records the generic endpoint-join argument
showing that the chosen prefix cannot change the route's final direction,
then specializes it to coordinated direct, delayed-lane, and ordinary
retained prefixes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Joining any prefix to the scaled Figure 7 occurrence suffix preserves
the unscaled suffix's final direction. -/
theorem
    joinAtEndpoint_scaledAngularOccurrenceSuffix_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (boundaryPrefix : List Cell)
    (boundary :
      boundaryPrefix.getLast? =
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            clause literal clauseIndex literalIndex)).head?) :
    AxisDirection.polylineLastDirection
        (joinAtEndpoint boundaryPrefix
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix placement
              (angularOccurrenceOrder source.erase routes)
              clause literal clauseIndex literalIndex))) =
      AxisDirection.polylineLastDirection
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          clause literal clauseIndex literalIndex) := by
  let suffix :=
    angularOccurrenceSuffix placement
      (angularOccurrenceOrder source.erase routes)
      clause literal clauseIndex literalIndex
  let middle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (OccurrenceSplitRing.angularFanBoundaryPositionAt
        placement literal.atom
        (incidenceRelativeOffset clause literal)
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex))
  have suffixHead :
      (scalePolyline retainedTerminalFanRoutingRefinement suffix).head? =
        some middle := by
    simp [suffix, middle, angularOccurrenceSuffix_head?]
  have prefixLast :
      boundaryPrefix.getLast? = some middle :=
    boundary.trans suffixHead
  have suffixLength : 2 ≤ suffix.length :=
    angularOccurrenceSuffix_length_ge_two
      placement
      (angularOccurrenceOrder source.erase routes)
      clause literal clauseIndex literalIndex
  have scaledSuffixLength :
      2 ≤
        (scalePolyline retainedTerminalFanRoutingRefinement suffix).length := by
    simpa [scalePolyline] using suffixLength
  rw [AxisDirection.polylineLastDirection_joinAtEndpoint
    prefixLast suffixHead scaledSuffixLength]
  exact
    AxisDirection.polylineLastDirection_scalePolyline
      retainedTerminalFanRoutingRefinement
      (by simp [retainedTerminalFanRoutingRefinement])
      suffix

/-- An ordinary retained copied-source occurrence splice ends in the
direction selected by its Figure 7 suffix. -/
theorem retainedAngularFanSplicedOccurrenceRoute_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase routes))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        source.erase routes)
    (endpoints :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  placement clause) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement clause literal))
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (retainedRoutes :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          RetainedRayPolyline
            (routes clauseIndex literalIndex))
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineLastDirection
        (retainedAngularFanSplicedOccurrenceRoute
          source placement routes clause literal
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          clause literal clauseIndex literalIndex) := by
  have boundaryValid :=
    retainedAngularFanBoundaryIncidenceRoutes_valid
      source placement routes fits certificate
      endpoints lengths retainedRoutes
      clauseMember literalMember
  unfold retainedAngularFanSplicedOccurrenceRoute
  exact
    joinAtEndpoint_scaledAngularOccurrenceSuffix_lastDirection
      source placement routes clause literal
      clauseIndex literalIndex
      (retainedAngularFanBoundaryIncidenceRoutes
        source routes clauseIndex literalIndex)
      (boundaryValid.2.1.trans
        (by
          simp [angularOccurrenceSuffix_head?]))

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- A validated coordinated direct occurrence ends in the direction of its
unchanged Figure 7 suffix. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_lastDirection
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
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    AxisDirection.polylineLastDirection
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choice
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) := by
  dsimp only
  unfold retainedFinalCoordinatedDirectOccurrenceRoute
  apply
    joinAtEndpoint_scaledAngularOccurrenceSuffix_lastDirection
  simpa [finalCoordinatedSource, finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes] using
    retainedFinalCoordinatedDirectOccurrenceRoute_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice clauseMember literalMember
      choiceLookup

/-- A genuine delayed-lane fallback occurrence ends in the direction of its
unchanged Figure 7 suffix. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_lastDirection
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
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    AxisDirection.polylineLastDirection
        (retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) := by
  dsimp only
  unfold retainedFinalEscapedFallbackOccurrenceRoute
  apply
    joinAtEndpoint_scaledAngularOccurrenceSuffix_lastDirection
  simpa [finalCoordinatedSource, finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes] using
    retainedFinalEscapedFallbackOccurrenceRoute_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
