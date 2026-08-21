/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceSiteMembership

/-! # Selecting global route occurrences at their clause sites -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Every neighboring route occurrence is selected again at its own lifted
clause site. -/
theorem CNFRouteOccurrence.mem_clauseRouteOccurrencesAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem : occurrence ∈ drawingCNFRouteOccurrences formula) :
    occurrence ∈ clauseRouteOccurrencesAt
      formula occurrence.clauseOccurrence := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, translatedMem⟩
  rcases List.mem_map.mp translatedMem with
    ⟨translate, translateMem, occurrenceEq⟩
  subst occurrence
  unfold clauseRouteOccurrencesAt CNFRouteOccurrence.clauseOccurrence
  apply List.mem_map.mpr
  refine ⟨taggedIncidence, ?_, rfl⟩
  exact List.mem_filter.mpr ⟨taggedIncidenceMem, by simp⟩

end LeanTrominoes.PeriodicOrthocrossing
