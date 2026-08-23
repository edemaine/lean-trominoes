/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundaryVariableRouteSiteFilter

/-! # Boundary-only routed-variable sites of copied occurrences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The same boundary reduction after the outer last-occurrence
deduplication used by the complete site stream. -/
theorem occurrenceVariableRouteSites_filter_cycle_dedup_eq_boundaryBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    ((occurrenceVariableRouteSites source).filter
        (cycleVariableRouteSiteAbsent source)).dedup =
      (occurrenceBoundaryVariableRouteSites source).dedup := by
  exact congrArg List.dedup
    (occurrenceVariableRouteSites_filter_cycle_eq_boundaryBlocks
      source positiveOffsets)

end PeriodicThreeSATThree
end LeanTrominoes
