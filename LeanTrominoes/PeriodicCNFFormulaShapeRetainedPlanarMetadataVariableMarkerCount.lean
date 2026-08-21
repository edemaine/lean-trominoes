/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableCount

/-! # Retained-formula count of metadata variable markers -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The metadata marker block is one marker per distinct variable occurrence
of the retained periodic planar-SAT formula. -/
theorem variableMarkers_eq_replicate_retainedCount
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    variableMarkers source =
      List.replicate
        (retainedDrawingPeriodicPlanarSATFormula
          source).variableOccurrences.dedup.length
        .variable := by
  unfold variableMarkers
  rw [positionedSource_variableCount_eq_retainedDrawing]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
