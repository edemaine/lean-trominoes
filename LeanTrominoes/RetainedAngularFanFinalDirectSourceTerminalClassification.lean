import LeanTrominoes.RetainedAngularFanFinalDirectSourceCrossClauseOrder

/-!
# Exact terminal classification of final direct choices

A successful final direct lookup represents a translated finite-atlas route.
Translation leaves its terminal vector unchanged, so the actual unscaled
final incidence classifies directly to the atlas direction and local length.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- Exact retained-terminal classification of the actual unscaled final
source route represented by a successful direct choice. -/
theorem retainedFinalDirectSourceRouteChoice_terminalClassify
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) =
      some
        ((retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1,
          (retainedDirectSourceLocalTerminalAt
            choice.kind choice.index).2) := by
  have represents :=
    retainedFinalDirectSourceRouteChoice_representsFinalRoute
      formula clauseIndex literalIndex choice choiceLookup
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
  have localClassified :=
    retainedDirectSourceLocalRouteAt_terminalClassify
      choice.kind choice.index
  have representedClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex)) =
        some (retainedDirectSourceLocalTerminalAt
          choice.kind choice.index) := by
    change retainedTerminalDirectionClassify
        (routeTerminalVector
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula clauseIndex literalIndex)) = _
    rw [← represents, routeTerminalVector_translatePolyline]
    exact localClassified
  simpa [retainedDirectSourceFanTerminalAt,
    retainedDirectSourcePrefixChoiceAt_direction_eq_localTerminal]
    using representedClassified

end PeriodicEightOccurrenceSplit
end LeanTrominoes
