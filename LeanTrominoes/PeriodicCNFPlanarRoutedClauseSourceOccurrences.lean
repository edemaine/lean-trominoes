/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarClauseRouteOccurrenceMembership
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-! # Source-terminal occurrences in routed clauses -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The source terminal of every neighboring incidence-route occurrence is a
literal variable in the complete routed-clause block. -/
theorem sourceTerminal_mem_drawingRoutedClauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem : occurrence ∈ drawingCNFRouteOccurrences formula) :
    (PlanarSATNode.carrier
        (.terminal (occurrence.sourceTerminal formula)) :
      PlanarSATNode Variable) ∈
        embeddedVariableOccurrences
          (drawingRoutedClauseFormula formula) := by
  rw [embeddedVariableOccurrences_drawingRoutedClauseFormula]
  apply List.mem_flatMap.mpr
  refine
    ⟨occurrence.clauseOccurrence,
      occurrence.clauseOccurrence_mem_drawingClauseRouteSites
        formula occurrenceMem, ?_⟩
  apply List.mem_map.mpr
  exact ⟨occurrence,
    occurrence.mem_clauseRouteOccurrencesAt formula occurrenceMem,
    rfl⟩

end LeanTrominoes.PeriodicOrthocrossing
