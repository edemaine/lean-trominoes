/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedOccurrences
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableTargetOccurrences

/-! # Retaining finite target-terminal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Under the occurrence-three bound, the target terminal of every
neighboring incidence-route occurrence survives in the retained finite
planar-SAT formula. -/
theorem targetTerminal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem : occurrence ∈ drawingCNFRouteOccurrences formula) :
    (Sum.inl
        (PlanarSATNode.carrier
          (.terminal (occurrence.targetTerminal formula))) :
      PlanarSATVariable Variable) ∈
        embeddedVariableOccurrences
          (retainedDrawingPlanarSATFormula formula) := by
  exact retainedDrawingPlanarSATFormula_terminal_routedVariable_occurrence
    formula (occurrence.targetTerminal formula)
    (targetTerminal_mem_drawingRoutedVariableFormula
      formula occurrences occurrenceMem)

end LeanTrominoes.PeriodicOrthocrossing
