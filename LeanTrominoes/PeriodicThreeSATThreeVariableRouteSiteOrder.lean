/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundaryVariableRouteSites
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteSiteUnion

/-! # Exact routed-variable site order after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- For current/next-slice source incidences, routed-variable sites consist
of the surviving positive-offset boundary sites followed by one complete
zero-offset block for each occurrence variable. -/
theorem drawingVariableRouteSites_formula_eq_boundary_append_rotated
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    drawingVariableRouteSites (formula source) =
      (occurrenceBoundaryVariableRouteSites source).dedup ++
        rotatedVariableRouteSiteBlocks source := by
  rw [drawingVariableRouteSites_formula_eq_occurrence_union_rotated]
  rw [decidableListUnion_eq_filteredDedup_append]
  have filteredSites :
      (occurrenceVariableRouteSites source).filter
          (decidableListAbsent
            (rotatedVariableRouteSiteBlocks source)) =
        (occurrenceVariableRouteSites source).filter
          (cycleVariableRouteSiteAbsent source) := by
    apply List.filter_congr
    intro site _
    rw [decidableListAbsent_eq_decide
      (rotatedVariableRouteSiteBlocks source) site
      (inferInstance : Decidable
        (site ∉ rotatedVariableRouteSiteBlocks source))]
    unfold cycleVariableRouteSiteAbsent
    exact Bool.decide_congr (by
      rw [not_iff_not,
        ← cycleLinkVariableRouteSites_dedup_eq_rotatedBlocks source]
      simp)
  rw [filteredSites]
  rw [occurrenceVariableRouteSites_filter_cycle_dedup_eq_boundaryBlocks
    source positiveOffsets]

end PeriodicThreeSATThree
end LeanTrominoes
