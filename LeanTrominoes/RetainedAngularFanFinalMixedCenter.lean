import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation

/-!
# Physical center equality for final direct/fallback pairs

The final mixed angular-order theorem compares canonical literal centers.
The positioned outer-route separation theorem uses fully refined physical
fan centers.  This module transports equality between those two coordinate
levels.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Equal canonical centers of a successful direct occurrence and a genuine
fallback occurrence induce the same fully refined positioned fan center. -/
theorem retainedFinalDirectFallback_positionedFanCenters_eq_of_sameCenter
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
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral) :
    retainedDirectSourcePositionedFanCenterAt
        choice.origin choice.kind choice.index =
      Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex)).getLastD
              (0, 0)) := by
  have directFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember
      directLiteralMember choiceLookup
  have fallbackEndpoint :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember
      fallbackLiteralMember).2
  have fallbackLastD :
      (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex).getLastD
          (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral := by
    rw [List.getLastD_eq_getLast?, fallbackEndpoint]
    rfl
  rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish,
    directFinish, centersEqual, scalePolyline_getLastD, fallbackLastD,
    Cell.scale_scale]
  rfl

end PeriodicOrthocrossing
end LeanTrominoes
