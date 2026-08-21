/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentMarkerBlockSemantics

/-! # Direct retained metadata segment-marker semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

/-- The direct block scan emits exactly two markers per segment counted by
the finite direct source shape. -/
theorem directRetainedPlanarMetadataSegmentMarkers_eq_replicate_shapeCount
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataSegmentMarkers decider symbols =
      List.replicate
        (2 * FormulaShape.routedSegmentCount
          (directSourceFormulaShape decider symbols))
        FormulaShapeDirectionOrdering.Token.variable := by
  unfold directRetainedPlanarMetadataSegmentMarkers
  exact flatMap_retainedSegmentMarkerBlock
    (directSourceFormulaShape decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction
