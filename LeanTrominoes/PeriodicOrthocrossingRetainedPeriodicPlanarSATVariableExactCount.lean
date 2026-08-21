/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCount
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablesNodup

/-! # Ordinary-length retained periodic planar-SAT variable count -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Under the standard source and drawing hypotheses, the distinct-variable
count of the retained formula is the ordinary length of the duplicate-free
canonical enumeration. -/
theorem retainedDrawingPeriodicPlanarSATFormula_dedup_length_eq_variables_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.dedup.length =
      (retainedDrawingPeriodicPlanarSATVariables formula).length := by
  rw [retainedDrawingPeriodicPlanarSATFormula_dedup_length_eq_variables
    formula occurrences wellFormed degree isLocal]
  rw [List.dedup_eq_self.mpr
    (retainedDrawingPeriodicPlanarSATVariables_nodup formula)]

end LeanTrominoes.PeriodicOrthocrossing
