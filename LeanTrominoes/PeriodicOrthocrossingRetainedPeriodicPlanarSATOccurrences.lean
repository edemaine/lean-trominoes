/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicization

/-! # Exact occurrences of the retained periodic planar-SAT formula -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The retained periodic occurrence list is the retained finite occurrence
list mapped by the variable component of planar-SAT normalization. -/
theorem retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_eq_map
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences =
      (embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula)).map fun atom =>
          (normalizePlanarSATVariable formula atom).1 := by
  simp [retainedDrawingPeriodicPlanarSATFormula,
    PeriodicCNF.variableOccurrences, embeddedVariableOccurrences,
    periodicizePlanarSATClause, periodicizePlanarSATLiteral,
    List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing
