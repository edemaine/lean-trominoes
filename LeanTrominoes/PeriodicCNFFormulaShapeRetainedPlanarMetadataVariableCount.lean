/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFDeduplicationExactVariableCount
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptors
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDegree

/-! # Exact variable count of retained planar metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Wrapping, gauging, anchor normalization, and clause deduplication do not
change the number of distinct retained planar-SAT variables. -/
theorem finalPositionedSource_variableCount_eq_retainedDrawing
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (FormulaShapeRetainedPlanarDirection.positionedSource
        source).erase.variableOccurrences.dedup.length =
      (retainedDrawingPeriodicPlanarSATFormula
        source).variableOccurrences.dedup.length := by
  rw [retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  rw [gaugedWrapped_deduplicate_variableOccurrences]
  rw [List.dedup_map_of_injective]
  · simp
  · intro first second equality
    exact congrArg WrappedPeriodicVariable.original equality

/-- The position-free metadata source has exactly the same distinct-variable
count as the retained periodic planar-SAT formula before wrapping. -/
theorem positionedSource_variableCount_eq_retainedDrawing
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (positionedSource source).erase.variableOccurrences.dedup.length =
      (retainedDrawingPeriodicPlanarSATFormula
        source).variableOccurrences.dedup.length := by
  have clausesEq :
      (positionedSource source).erase.clauses =
        (FormulaShapeRetainedPlanarDirection.positionedSource
          source).erase.clauses := by
    rw [positionedSource_erase_clauses,
      positionedSource_erase_clauses_eq]
  have occurrencesEq :
      (positionedSource source).erase.variableOccurrences =
        (FormulaShapeRetainedPlanarDirection.positionedSource
          source).erase.variableOccurrences := by
    unfold PeriodicCNF.variableOccurrences
    rw [clausesEq]
  rw [occurrencesEq]
  exact finalPositionedSource_variableCount_eq_retainedDrawing source

/-- The exact metadata marker suffix length is the retained planar-SAT
distinct-variable count. -/
theorem variableMarkers_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (variableMarkers source).length =
      (retainedDrawingPeriodicPlanarSATFormula
        source).variableOccurrences.dedup.length := by
  unfold variableMarkers
  rw [List.length_replicate]
  exact positionedSource_variableCount_eq_retainedDrawing source

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
