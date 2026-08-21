/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataAtomMarkerData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentMarkerData

/-! # Combined direct retained segment and atom markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

/-- Emit the segment-terminal and source-atom marker blocks in one finite
scan.  Their tokens are indistinguishable in the final unary marker suffix. -/
def retainedSegmentAtomMarkerBlock :
    FormulaShape.Token → List FormulaShapeDirectionOrdering.Token
  | token =>
      retainedSegmentMarkerBlock token ++ retainedAtomMarkerBlock token

def directRetainedPlanarMetadataSegmentAtomMarkers
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormulaShape decider symbols).flatMap
    retainedSegmentAtomMarkerBlock

end LeanTrominoes.PeriodicCNFStripReduction
