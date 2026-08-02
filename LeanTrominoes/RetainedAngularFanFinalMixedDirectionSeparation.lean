import LeanTrominoes.RetainedAngularFanFinalMixedAlignedDirectionSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceMixedDirectionInequality
import LeanTrominoes.RetainedAngularFanFinalFallbackSegmentClassification

/-!
# Terminal-direction separation for final mixed pairs

An aligned successful direct segment is separated from a fallback direction
by inherited source planarity.  An oblique direct segment is separated from
the fallback's axis-aligned final segment by exact terminal classification.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- A successful direct occurrence and a failed fallback occurrence from
different final source clauses have distinct terminal directions whenever
they end at the same canonical variable center. -/
theorem
    retainedFinalDirectFallbackTerminalDirections_ne_of_sameCenter
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
          fallbackClause fallbackLiteral) :
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 ≠
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1 := by
  by_cases directAligned : choice.sourceSegment.IsAxisAligned
  · exact
      retainedFinalDirectFallbackTerminalDirections_ne_of_sameCenter_of_directSegment_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup fallbackChoiceNone
        clauseIndicesDifferent centersEqual directAligned
  · let fallbackRoute :=
      finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex
    let fallbackTerminal : RetainedTerminalData :=
      classifiedRetainedTerminalData
        (routeTerminalVector fallbackRoute)
    have fallbackClassified :
        retainedTerminalDirectionClassify
            (Cell.sub
              (polylineLastEntrance fallbackRoute)
              (fallbackRoute.getLastD (0, 0))) =
          some fallbackTerminal := by
      simpa only [fallbackRoute, fallbackTerminal] using
        finalCoordinatedSourceRoute_finalSegment_classified
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          fallbackClauseMember fallbackLiteralMember
    have fallbackAligned :
        (GridSegment.mk
          (polylineLastEntrance fallbackRoute)
          (fallbackRoute.getLastD (0, 0))).IsAxisAligned := by
      simpa only [fallbackRoute] using
        finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          fallbackClauseMember fallbackLiteralMember fallbackChoiceNone
    rw [show
      finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex =
        fallbackRoute from rfl]
    rw [show
      classifiedRetainedTerminalData
          (routeTerminalVector fallbackRoute) =
        fallbackTerminal from rfl]
    exact
      choice.direction_ne_of_otherTerminal_aligned
        (otherStart := polylineLastEntrance fallbackRoute)
        (otherFinish := fallbackRoute.getLastD (0, 0))
        (otherTerminal := fallbackTerminal)
        fallbackClassified fallbackAligned directAligned

end PeriodicOrthocrossing
end LeanTrominoes
