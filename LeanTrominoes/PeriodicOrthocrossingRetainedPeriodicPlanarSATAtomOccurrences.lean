/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedAtomOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATOccurrences

/-! # Periodic occurrences of represented source atoms -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every represented translation-zero source site survives periodicization
as its source protovariable. -/
theorem atom_mem_retainedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {atom : Variable}
    (siteMem : (atom, (0, 0)) ∈ drawingVariableRouteSites formula) :
    PeriodicPlanarSATVariable.atom atom ∈
      (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences := by
  rw [retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_eq_map]
  apply List.mem_map.mpr
  exact
    ⟨Sum.inl (PlanarSATNode.atom (atom, (0, 0))),
      variableRouteSiteAtom_mem_retainedDrawingPlanarSATFormula
        formula siteMem,
      rfl⟩

end LeanTrominoes.PeriodicOrthocrossing
