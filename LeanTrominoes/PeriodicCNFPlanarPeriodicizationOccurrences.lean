/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarPeriodicization
import LeanTrominoes.PlanarThreeSATOcurrences

/-! # Variable occurrences under planar-SAT periodicization -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Periodicizing an embedded formula maps its finite occurrence list by the
variable component of planar-SAT normalization. -/
theorem periodicizePlanarSATFormula_variableOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (finiteFormula : List (EmbeddedClause (PlanarSATVariable Variable))) :
    (⟨finiteFormula.map (periodicizePlanarSATClause formula)⟩ :
        PeriodicCNF (PeriodicPlanarSATVariable Variable)).variableOccurrences =
      (embeddedVariableOccurrences finiteFormula).map fun atom =>
        (normalizePlanarSATVariable formula atom).1 := by
  simp [PeriodicCNF.variableOccurrences, embeddedVariableOccurrences,
    periodicizePlanarSATClause, periodicizePlanarSATLiteral,
    List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing
