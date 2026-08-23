/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceCurrentVariableRouteSiteFilter
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceNextVariableRouteSiteFilter

/-! # Boundary-only copied variable-route site filtering -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Filtering the copied-occurrence site prefix against the later cycle
suffix retains exactly the three boundary sites of each positive-offset
source incidence, in source incidence order. -/
theorem occurrenceVariableRouteSites_filter_cycle_eq_boundaryBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (occurrenceVariableRouteSites source).filter
        (cycleVariableRouteSiteAbsent source) =
      occurrenceBoundaryVariableRouteSites source := by
  unfold occurrenceVariableRouteSites occurrenceBoundaryVariableRouteSites
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro incidence incidenceMember
  have atomMember : incidence.literal.atom ∈
      allOccurrenceVariables source := by
    rw [← occurrenceIncidences_atoms source]
    exact List.mem_map_of_mem incidenceMember
  rcases positiveOffsets incidence incidenceMember with
    current | next
  · rw [current,
      filter_currentVariableRouteSiteBlock_against_cycle
        source incidence.literal.atom atomMember]
    simp
  · rw [next,
      filter_nextVariableRouteSiteBlock_against_cycle
        source incidence.literal.atom atomMember]
    simp

end PeriodicThreeSATThree
end LeanTrominoes
