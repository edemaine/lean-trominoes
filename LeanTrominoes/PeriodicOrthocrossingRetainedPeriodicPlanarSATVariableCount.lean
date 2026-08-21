/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCoverage
import LeanTrominoes.ListDedupLength

/-! # Exact retained periodic planar-SAT variable count -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The number of distinct variables in the retained periodic formula is the
deduplicated length of the canonical enumeration. -/
theorem retainedDrawingPeriodicPlanarSATFormula_dedup_length_eq_variables
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
      (retainedDrawingPeriodicPlanarSATVariables formula).dedup.length := by
  apply List.dedup_length_eq_of_mem_iff
  intro atom
  exact mem_retainedDrawingPeriodicPlanarSATFormula_iff_mem_variables
    formula occurrences wellFormed degree isLocal atom

end LeanTrominoes.PeriodicOrthocrossing
