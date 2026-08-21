/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedOccurrences
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableOccurrences

/-! # Retained finite occurrences of represented source atoms -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every represented variable-route site contributes its central atom to the
complete retained finite planar-SAT formula. -/
theorem variableRouteSiteAtom_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    (Sum.inl (PlanarSATNode.atom site) : PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  exact retainedDrawingPlanarSATFormula_atom_routedVariable_occurrence
    formula site
    (routedVariableCenter_mem_drawingRoutedVariableFormula
      formula siteMem)

end LeanTrominoes.PeriodicOrthocrossing
