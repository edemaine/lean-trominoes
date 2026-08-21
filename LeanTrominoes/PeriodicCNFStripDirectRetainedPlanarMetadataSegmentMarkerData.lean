/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDrawingSegmentCount
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeData

/-! # Direct retained metadata segment-marker data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- A clause token contributes two markers per routed segment attributed to
its finite profile; a variable token contributes four markers for its two
variable-side fanout segments. -/
def retainedSegmentMarkerBlock :
    FormulaShape.Token → List FormulaShapeDirectionOrdering.Token
  | .clause profile =>
      List.replicate
        (2 * PeriodicCNF.ClauseProfile.routeSegmentCount profile) .variable
  | .variable => List.replicate 4 .variable

/-- Emit the routed-segment portion of the retained metadata variable-marker
suffix from the direct finite formula shape. -/
def directRetainedPlanarMetadataSegmentMarkers
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormulaShape decider symbols).flatMap
    retainedSegmentMarkerBlock

end LeanTrominoes.PeriodicCNFStripReduction
