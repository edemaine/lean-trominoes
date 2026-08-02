import LeanTrominoes.RetainedAngularFanFinalDirectSourceTerminalClassification
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherCycleSeparation

/-!
# Terminal classification of positioned direct source segments

A direct source choice remembers a translated copy of one finite-atlas
incidence.  This module classifies the backwards vector of that positioned
segment directly, without recovering it through the full final-route
selector.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- The endpoint vector of every finite-atlas direct incidence has the
direction and length recorded by its fan and local terminal data. -/
private theorem retainedDirectSourceLocalSegment_terminalClassify :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      retainedTerminalDirectionClassify
          (Cell.sub
            ((retainedDirectSourceLocalRouteAt kind index).headD (0, 0))
            ((retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0))) =
        some
          ((retainedDirectSourceFanTerminalAt kind index).1,
            (retainedDirectSourceLocalTerminalAt kind index).2) := by
  native_decide

/-- Translating a selected direct incidence preserves the exact terminal
classification of its represented source segment. -/
theorem RetainedDirectSourceRouteChoice.sourceSegment_terminalClassify
    (choice : RetainedDirectSourceRouteChoice) :
    retainedTerminalDirectionClassify
        (Cell.sub choice.sourceSegment.start choice.sourceSegment.finish) =
      some
        ((retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1,
          (retainedDirectSourceLocalTerminalAt
            choice.kind choice.index).2) := by
  have localClassified :=
    retainedDirectSourceLocalSegment_terminalClassify
      choice.kind choice.index
  simpa [RetainedDirectSourceRouteChoice.sourceSegment,
    Cell.add, Cell.sub] using localClassified

end PeriodicEightOccurrenceSplit
end LeanTrominoes
