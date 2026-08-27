/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedTailData

/-! # Genuine-index semantics of normalized direct-source tail queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Gadget

/-- On a genuine dependent atlas index, the total query selects the
origin-zero normalized route word. -/
theorem retainedDirectSourceNormalizedDirectionsOfTailQuery_index
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    retainedDirectSourceNormalizedDirectionsOfTailQuery
        (retainedDirectSourceNormalizedTailQueryOfIndex kind index slot) =
      unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
            slot)) := by
  unfold retainedDirectSourceNormalizedDirectionsOfTailQuery
    retainedDirectSourceNormalizedTailQueryOfIndex
  simp only [index.isLt, dite_true]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
