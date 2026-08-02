import LeanTrominoes.RetainedAngularFanFinalDirectSourceAlignedOrthogonality
import LeanTrominoes.RetainedAngularFanFinalCrossClauseSourceRouteSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceTerminalClassification
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation
import LeanTrominoes.RetainedTerminalDataEndpointSeparation

/-!
# Aligned terminal-direction separation for final mixed pairs

When a successful direct source segment is axis-aligned, its original final
source route is orthogonal.  A failed fallback route is orthogonal as well.
At a common variable endpoint, inherited continuous source planarity then
forces their classified terminal directions to differ.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- An aligned successful direct occurrence and a failed fallback occurrence
from different final source clauses have different terminal directions at a
shared canonical variable center. -/
theorem
    retainedFinalDirectFallbackTerminalDirections_ne_of_sameCenter_of_directSegment_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex =
        some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
    (directAligned : choice.sourceSegment.IsAxisAligned) :
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 ≠
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1 := by
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  let fallbackTerminal : RetainedTerminalData :=
    classifiedRetainedTerminalData
      (routeTerminalVector fallbackRoute)
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackLength : 2 ≤ fallbackRoute.length := by
    simpa [fallbackRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directOrthogonal : OrthogonalPolyline directRoute := by
    simpa [directRoute] using
      retainedFinalDirectSourceRoute_orthogonal_of_sourceSegment_axisAligned
        formula directClauseIndex directLiteralIndex
        choice choiceLookup directAligned
  have fallbackOrthogonal : OrthogonalPolyline fallbackRoute := by
    simpa [fallbackRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        fallbackClauseMember fallbackLiteralMember fallbackChoiceNone
  have directEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have sameFinish : directRoute.getLast? = fallbackRoute.getLast? := by
    simpa [directRoute, fallbackRoute] using
      directEndpoints.2.trans
        (centersEqual ▸ fallbackEndpoints.2.symm)
  have sourceRoutesAvoid :
      RoutesAvoidEachOther directRoute fallbackRoute := by
    simpa [directRoute, fallbackRoute] using
      retainedFinalCrossClauseSourceRoutes_avoidEachOther
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        clauseIndicesDifferent
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) =
        some directTerminal := by
    simpa only [directRoute, directTerminal] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have fallbackClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector fallbackRoute) =
        some fallbackTerminal := by
    simpa only [fallbackRoute, fallbackTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        fallbackClauseMember fallbackLiteralMember
  rw [show
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 =
      directTerminal.1 from rfl]
  rw [show
    finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex =
      fallbackRoute from rfl]
  rw [show
    classifiedRetainedTerminalData
        (routeTerminalVector fallbackRoute) =
      fallbackTerminal from rfl]
  exact
    retainedTerminalDataDirections_ne_of_routesAvoidEachOther
      directTerminal fallbackTerminal
      directLength fallbackLength
      directOrthogonal fallbackOrthogonal
      sameFinish sourceRoutesAvoid
      directClassified fallbackClassified

end PeriodicOrthocrossing
end LeanTrominoes
