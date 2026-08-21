/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerBlockSemantics

/-! # Direct combined segment and atom marker semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

theorem directRetainedPlanarMetadataSegmentAtomMarkers_eq_replicate_shapeCounts
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataSegmentAtomMarkers decider symbols =
      List.replicate
        (2 * FormulaShape.routedSegmentCount
            (directSourceFormulaShape decider symbols) +
          FormulaShape.variableCount
            (directSourceFormulaShape decider symbols))
        FormulaShapeDirectionOrdering.Token.variable := by
  unfold directRetainedPlanarMetadataSegmentAtomMarkers
  exact flatMap_retainedSegmentAtomMarkerBlock
    (directSourceFormulaShape decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction
