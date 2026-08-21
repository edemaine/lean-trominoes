/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedOccurrences
import LeanTrominoes.PeriodicCNFPlanarRoutedClauseSourceOccurrences

/-! # Retaining finite source-terminal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The source terminal of every neighboring incidence-route occurrence
survives in the retained finite planar-SAT formula. -/
theorem sourceTerminal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem : occurrence ∈ drawingCNFRouteOccurrences formula) :
    (Sum.inl
        (PlanarSATNode.carrier
          (.terminal (occurrence.sourceTerminal formula))) :
      PlanarSATVariable Variable) ∈
        embeddedVariableOccurrences
          (retainedDrawingPlanarSATFormula formula) := by
  exact retainedDrawingPlanarSATFormula_terminal_routedClause_occurrence
    formula (occurrence.sourceTerminal formula)
    (sourceTerminal_mem_drawingRoutedClauseFormula formula occurrenceMem)

end LeanTrominoes.PeriodicOrthocrossing
