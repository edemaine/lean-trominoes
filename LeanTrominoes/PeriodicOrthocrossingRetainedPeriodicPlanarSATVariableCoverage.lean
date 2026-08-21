/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCompleteness

/-! # Exact coverage of retained periodic planar-SAT variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- With the standard drawing hypotheses and occurrence-three bound, the
formula occurrence set is exactly the canonical four-family enumeration. -/
theorem mem_retainedDrawingPeriodicPlanarSATFormula_iff_mem_variables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PeriodicPlanarSATVariable Variable) :
    atom ∈ (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences ↔
      atom ∈ retainedDrawingPeriodicPlanarSATVariables formula := by
  constructor
  · intro atomMem
    apply (mem_retainedDrawingPeriodicPlanarSATVariables_iff
      formula atom).mpr
    exact retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_valid
      formula wellFormed degree isLocal atomMem
  · intro atomMem
    apply retainedDrawingPeriodicPlanarSATVariableValid_mem
      formula occurrences
    exact (mem_retainedDrawingPeriodicPlanarSATVariables_iff
      formula atom).mp atomMem

end LeanTrominoes.PeriodicOrthocrossing
