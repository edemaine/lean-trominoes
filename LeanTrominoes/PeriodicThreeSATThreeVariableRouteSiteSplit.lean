/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundaryVariableRouteSites

/-! # Copied-prefix/cycle-suffix split of routed-variable sites -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Before evaluating last-occurrence deduplication, the split formula's site
stream is exactly its copied-incidence prefix followed by its cycle suffix. -/
theorem drawingVariableRouteSites_formula_eq_dedup_occurrence_append_cycle
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    drawingVariableRouteSites (formula source) =
      (occurrenceVariableRouteSites source ++
        cycleLinkVariableRouteSites source).dedup := by
  rw [drawingVariableRouteSites_eq_dedup_incidenceBlocks]
  rw [formula_incidencesWithMetadata_eq_occurrence_append_cycle]
  rw [← cycleLinkIncidences_eq_cycleIncidences]
  rw [List.flatMap_append]
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
