/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableMarkerCount
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableExactCount

/-! # Canonical enumeration of retained metadata variable markers -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Under the standard retained-planar hypotheses, the abstract marker block
is exactly one marker per member of the canonical four-family enumeration. -/
theorem variableMarkers_eq_replicate_retainedVariables
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    variableMarkers source =
      List.replicate
        (retainedDrawingPeriodicPlanarSATVariables source).length
        .variable := by
  rw [variableMarkers_eq_replicate_retainedCount]
  rw [retainedDrawingPeriodicPlanarSATFormula_dedup_length_eq_variables_length
    source occurrences wellFormed degree isLocal]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
