/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentMarkerData

/-! # Finite block semantics of retained segment markers -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

/-- The fixed block scan emits two markers per segment counted by a finite
formula shape. -/
theorem flatMap_retainedSegmentMarkerBlock
    (shape : List FormulaShape.Token) :
    shape.flatMap retainedSegmentMarkerBlock =
      List.replicate (2 * FormulaShape.routedSegmentCount shape)
        FormulaShapeDirectionOrdering.Token.variable := by
  induction shape with
  | nil => rfl
  | cons token shape induction =>
      rw [List.flatMap_cons, induction]
      cases token with
      | clause profile =>
          simp only [retainedSegmentMarkerBlock]
          rw [← List.replicate_add]
          congr 1
          simp [FormulaShape.routedSegmentCount,
            FormulaShape.clauseProfiles, FormulaShape.variableCount,
            FormulaShape.variableMarkers]
          omega
      | «variable» =>
          simp only [retainedSegmentMarkerBlock]
          rw [← List.replicate_add]
          congr 1
          simp [FormulaShape.routedSegmentCount,
            FormulaShape.clauseProfiles, FormulaShape.variableCount,
            FormulaShape.variableMarkers]
          omega

end LeanTrominoes.PeriodicCNFStripReduction
