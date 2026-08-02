import LeanTrominoes.RetainedAngularFanDirectFallbackOuterReduction
import LeanTrominoes.RetainedAngularFanFinalMixedOrder
import LeanTrominoes.RetainedAngularFanFinalMixedDirectionSeparation
import LeanTrominoes.RetainedTerminalDirectionAlignment

/-!
# Strict angular order of final direct/fallback pairs

The final occurrence ordering gives a weak comparison of terminal-direction
ranks because collinear terminal rays are ordered by a radial tie-break.  If
the direct and fallback directions are different, injectivity of angular rank
upgrades that comparison to the strict order consumed by the outer-route
separation theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Compatible slot and direction order becomes strict when the two terminal
directions are different. -/
theorem
    directFallbackStrictAngularOrderCompatible_of_compatible_of_ne
    (choice : RetainedDirectSourceRouteChoice)
    (fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot)
    (compatible :
      RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
        choice fallbackDirection directSlot fallbackSlot)
    (directionsDifferent :
      (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1 ≠ fallbackDirection) :
    DirectFallbackStrictAngularOrderCompatible
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      fallbackDirection directSlot fallbackSlot := by
  unfold RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible at compatible
  unfold DirectFallbackStrictAngularOrderCompatible
  rcases compatible with
      ⟨slotsLt, ranksLe⟩ |
      ⟨slotsLt, ranksLe⟩
  · exact Or.inl
      ⟨slotsLt,
        Nat.lt_of_le_of_ne ranksLe fun ranksEqual =>
          directionsDifferent
            (RetainedTerminalDirection.angularRank_injective ranksEqual)⟩
  · exact Or.inr
      ⟨slotsLt,
        Nat.lt_of_le_of_ne ranksLe fun ranksEqual =>
          directionsDifferent
            (RetainedTerminalDirection.angularRank_injective ranksEqual.symm)⟩

/-- Compatible direct/fallback order is strict when their successfully
classified terminal segments have different axis-alignment status. -/
theorem
    directFallbackStrictAngularOrderCompatible_of_compatible_of_alignment_ne
    (choice : RetainedDirectSourceRouteChoice)
    (fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot)
    {directStart directFinish fallbackStart fallbackFinish : Cell}
    {directLength fallbackLength : Nat}
    (compatible :
      RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
        choice fallbackDirection directSlot fallbackSlot)
    (directClassified :
      retainedTerminalDirectionClassify
          (Cell.sub directStart directFinish) =
        some
          ((retainedDirectSourceFanTerminalAt
            choice.kind choice.index).1, directLength))
    (fallbackClassified :
      retainedTerminalDirectionClassify
          (Cell.sub fallbackStart fallbackFinish) =
        some (fallbackDirection, fallbackLength))
    (fallbackAligned :
      (GridSegment.mk fallbackStart fallbackFinish).IsAxisAligned)
    (directNotAligned :
      ¬(GridSegment.mk directStart directFinish).IsAxisAligned) :
    DirectFallbackStrictAngularOrderCompatible
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      fallbackDirection directSlot fallbackSlot := by
  apply
    directFallbackStrictAngularOrderCompatible_of_compatible_of_ne
      choice fallbackDirection directSlot fallbackSlot compatible
  exact
    (retainedTerminalDirections_ne_of_segment_alignment_ne
      fallbackClassified directClassified
      fallbackAligned directNotAligned).symm

/-- Different final source clauses ending at the same canonical variable
center have the strict direct/fallback angular order required by outer-fan
separation. -/
theorem
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_sameCenter
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
    DirectFallbackStrictAngularOrderCompatible
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
      (retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex)
      (retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex) := by
  apply
    directFallbackStrictAngularOrderCompatible_of_compatible_of_ne
  · exact
      retainedFinalDirectFallback_angularOrderCompatible_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup clauseIndicesDifferent centersEqual
  · exact
      retainedFinalDirectFallbackTerminalDirections_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup fallbackChoiceNone
        clauseIndicesDifferent centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
