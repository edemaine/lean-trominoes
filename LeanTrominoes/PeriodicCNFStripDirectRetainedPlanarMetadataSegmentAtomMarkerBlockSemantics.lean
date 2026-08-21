/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerData

/-! # Finite block semantics of combined segment and atom markers -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

/-- The combined scan emits two terminal markers per routed segment and one
marker per source variable represented by the finite shape. -/
theorem flatMap_retainedSegmentAtomMarkerBlock
    (shape : List FormulaShape.Token) :
    shape.flatMap retainedSegmentAtomMarkerBlock =
      List.replicate
        (2 * FormulaShape.routedSegmentCount shape +
          FormulaShape.variableCount shape)
        FormulaShapeDirectionOrdering.Token.variable := by
  induction shape with
  | nil => rfl
  | cons token shape induction =>
      rw [List.flatMap_cons, induction]
      cases token with
      | clause profile =>
          simp only [retainedSegmentAtomMarkerBlock,
            retainedSegmentMarkerBlock, retainedAtomMarkerBlock,
            List.append_nil]
          rw [← List.replicate_add]
          congr 1
          simp [FormulaShape.routedSegmentCount,
            FormulaShape.clauseProfiles, FormulaShape.variableCount,
            FormulaShape.variableMarkers]
          omega
      | «variable» =>
          simp only [retainedSegmentAtomMarkerBlock,
            retainedSegmentMarkerBlock, retainedAtomMarkerBlock]
          rw [← List.replicate_one, ← List.replicate_add,
            ← List.replicate_add]
          congr 1
          simp [FormulaShape.routedSegmentCount,
            FormulaShape.clauseProfiles, FormulaShape.variableCount,
            FormulaShape.variableMarkers]
          omega

end LeanTrominoes.PeriodicCNFStripReduction
