/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarClauseSiteMembership

/-! # Represented sites selected by global route occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The lifted clause site reached by every neighboring route occurrence is
present in the finite clause-site enumeration. -/
theorem CNFRouteOccurrence.clauseOccurrence_mem_drawingClauseRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem : occurrence ∈ drawingCNFRouteOccurrences formula) :
    occurrence.clauseOccurrence ∈ drawingClauseRouteSites formula := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, translatedMem⟩
  rcases List.mem_map.mp translatedMem with
    ⟨translate, translateMem, occurrenceEq⟩
  subst occurrence
  have incidenceMem :
      taggedIncidence.1 ∈ PeriodicCNF.incidencesWithMetadata formula :=
    List.fst_mem_of_mem_zipIdx taggedIncidenceMem
  exact CNFIncidence.clauseSite_mem_drawingClauseRouteSites
    formula incidenceMem translateMem

end LeanTrominoes.PeriodicOrthocrossing
