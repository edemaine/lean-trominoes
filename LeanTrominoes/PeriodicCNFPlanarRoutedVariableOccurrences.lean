/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableCenterOccurrence

/-! # Central-atom occurrences in routed variable gadgets -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The central atom of every represented site occurs in the complete routed
variable-gadget block. -/
theorem routedVariableCenter_mem_drawingRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    PlanarSATNode.atom site ∈ embeddedVariableOccurrences
      (drawingRoutedVariableFormula formula) := by
  unfold drawingRoutedVariableFormula
  rw [embeddedVariableOccurrences_flatMap]
  apply List.mem_flatMap.mpr
  exact ⟨site, siteMem,
    routedVariableCenter_mem_routedVariableFormulaAt formula siteMem⟩

end LeanTrominoes.PeriodicOrthocrossing
