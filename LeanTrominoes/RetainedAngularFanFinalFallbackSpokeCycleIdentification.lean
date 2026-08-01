import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification
import LeanTrominoes.RetainedAngularFanSourceCompleteOwnCycleSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitSpokeCycleSeparation

/-!
# Identifying fallback spokes with final occurrence suffixes

The generic fallback certificate centers a factor-eight Figure 7 spoke at
the copied source route's old variable endpoint.  The final route family
describes the same spoke as a scaled positioned occurrence suffix.  Equal
occurrence slots and the validated common boundary head identify those two
translations exactly.

Because the local spoke is nonempty, the spoke equality also identifies the
generic centered implication cycle with the corresponding periodically
translated and scaled positioned cycle lift.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Total presentation-indexed inner implication route centered at a
retained source-variable position. -/
def retainedTerminalFanInnerCycleRoutesAt
    (center : Cell)
    (cycleClauseIndex literalIndex : Nat) :
    List Cell :=
  translatePolyline center
    (translatePolyline
      (Cell.sub (0, 0)
        (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
      (scalePolyline retainedTerminalFanRoutingRefinement
        (cycleRoutes cycleClauseIndex literalIndex)))

/-- At valid presentation indices, the total centered cycle lookup is the
corresponding vertex-indexed inner cycle route. -/
theorem retainedTerminalFanInnerCycleRoutesAt_eq_innerCycleRouteAt
    (center : Cell)
    (cycleClauseIndex literalIndex : Nat)
    (cycleClauseIndexLt :
      cycleClauseIndex < presentedCycleVertices.length)
    (literalIndexLt : literalIndex < 2) :
    retainedTerminalFanInnerCycleRoutesAt
        center cycleClauseIndex literalIndex =
      retainedTerminalFanInnerCycleRouteAt
        center
        (presentedCycleVertices.getD
          cycleClauseIndex .separator)
        ⟨literalIndex, literalIndexLt⟩ := by
  simp [retainedTerminalFanInnerCycleRoutesAt,
    retainedTerminalFanInnerCycleRouteAt,
    retainedTerminalFanInnerCycleRoute,
    cycleRoutes, cycleClauseIndexLt]

/-- A centered fallback spoke is exactly the scaled positioned occurrence
suffix when their slots agree and their validated boundary heads agree. -/
theorem
    retainedTerminalFanFigure7SpokeRouteAt_eq_scaledAngularOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (slotVal :
      slot.val =
        angularOccurrenceIndex order literal
          clauseIndex literalIndex)
    (headsEqual :
      (retainedTerminalFanFigure7SpokeRouteAt
        center slot).head? =
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex)).head?) :
    retainedTerminalFanFigure7SpokeRouteAt center slot =
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex) := by
  rw [retainedTerminalFanFigure7SpokeRouteAt,
    translatePolyline_add,
    scalePolyline_angularOccurrenceSuffix_eq_translate]
      at headsEqual ⊢
  rw [slotVal] at headsEqual ⊢
  apply translatePolyline_eq_of_head?_eq _ _ _ ?_ headsEqual
  cases angularPortOfIndex
      (angularOccurrenceIndex order literal
        clauseIndex literalIndex) <;>
    native_decide

/-- Equality of a centered fallback spoke with a scaled occurrence suffix
forces equality of the corresponding total centered cycle lookup and
periodically lifted positioned cycle route. -/
theorem
    retainedTerminalFanInnerCycleRoutesAt_eq_scaledTranslatedPositionedCycleRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (slotVal :
      slot.val =
        angularOccurrenceIndex order literal
          clauseIndex literalIndex)
    (spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex))
    (cycleClauseIndex cycleLiteralIndex : Nat) :
    retainedTerminalFanInnerCycleRoutesAt
        center cycleClauseIndex cycleLiteralIndex =
      scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline
          ((placement sourcePlacement).translation
            (incidenceRelativeOffset clause literal))
          (positionedCycleRoutes sourcePlacement literal.atom
            cycleClauseIndex cycleLiteralIndex)) := by
  have translatedSpokesEqual := spokeEqual
  rw [retainedTerminalFanFigure7SpokeRouteAt,
    translatePolyline_add,
    scalePolyline_angularOccurrenceSuffix_eq_translate,
    slotVal] at translatedSpokesEqual
  let localRoute :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (spokeRoute
        (angularPortOfIndex
          (angularOccurrenceIndex order literal
            clauseIndex literalIndex)))
  have localRouteNonempty : localRoute ≠ [] := by
    unfold localRoute scalePolyline
    cases angularPortOfIndex
        (angularOccurrenceIndex order literal
          clauseIndex literalIndex) <;>
      native_decide
  have offsetsEqual :
      Cell.add
          (Cell.sub (0, 0)
            (Cell.scale retainedTerminalFanRoutingRefinement
              (12, 12)))
          center =
        Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanOccurrenceOrigin sourcePlacement
            literal.atom
            (incidenceRelativeOffset clause literal)) := by
    exact
      translatePolyline_offsets_eq_of_nonempty
        _ _ localRoute localRouteNonempty
        (by simpa [localRoute] using translatedSpokesEqual)
  rw [
    scalePolyline_translatedPositionedCycleRoutes_eq_translate]
  unfold retainedTerminalFanInnerCycleRoutesAt
  rw [translatePolyline_add, offsetsEqual]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
