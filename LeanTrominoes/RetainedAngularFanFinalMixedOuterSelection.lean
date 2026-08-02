import LeanTrominoes.RetainedAngularFanFinalMixedBoundaryAssembly
import LeanTrominoes.RetainedAngularFanDirectSourcePositionedScaledFallbackSeparation

/-!
# Selected final fallback outer-route separation

The final fallback router selects the delayed-lane outer route exactly for a
singleton unscaled source prefix and the ordinary outer route otherwise.
Once strict angular order and equality of physical centers are available,
both branches follow from positioned direct/fallback separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Under strict compatible order at a common physical center, a selected
direct route avoids whichever fallback outer replacement the final router
chooses. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalCoordinatedFallbackOuterReplacement_of_order
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (fallbackClauseIndex fallbackLiteralIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    (angularOrder :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      let rawTerminal :=
        classifiedRetainedTerminalData
          (routeTerminalVector rawRoute)
      let fallbackSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        rawTerminal.1 directSlot fallbackSlot)
    (centersEqual :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline retainedAngularFanSourceClearanceFactor
            rawRoute).getLastD (0, 0)))
    (fallbackLengthPositive :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      0 < (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)).2)
    (fallbackEscapeStrict :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      let rawTerminal :=
        classifiedRetainedTerminalData
          (routeTerminalVector rawRoute)
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor rawTerminal)) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedFinalCoordinatedFallbackOuterReplacement
        formula fallbackLiteral
        fallbackClauseIndex fallbackLiteralIndex) := by
  let rawRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        rawRoute).getLastD (0, 0))
  unfold retainedFinalCoordinatedFallbackOuterReplacement
  dsimp only
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [if_pos (by simpa only [rawRoute] using singletonPrefix)]
    exact
      choice.completeRoute_strictlyAvoids_scaledEscapedFallbackAt_of_order
        directSlot rawTerminal fallbackSlot fallbackCenter
        (by simpa only [rawRoute, fallbackCenter] using centersEqual)
        (by simpa only [rawRoute, rawTerminal, fallbackSlot] using angularOrder)
        (by simpa only [rawRoute, rawTerminal] using fallbackLengthPositive)
        (by simpa only [rawRoute, rawTerminal] using fallbackEscapeStrict)
  · rw [if_neg (by simpa only [rawRoute] using singletonPrefix)]
    exact
      choice.completeRoute_strictlyAvoids_scaledOrdinaryFallbackAt_of_order
        directSlot rawTerminal fallbackSlot fallbackCenter
        (by simpa only [rawRoute, fallbackCenter] using centersEqual)
        (by simpa only [rawRoute, rawTerminal, fallbackSlot] using angularOrder)
        (by simpa only [rawRoute, rawTerminal] using fallbackLengthPositive)
        (Nat.zero_lt_of_lt
          (by simpa only [rawRoute, rawTerminal] using fallbackEscapeStrict))

end PeriodicOrthocrossing
end LeanTrominoes
