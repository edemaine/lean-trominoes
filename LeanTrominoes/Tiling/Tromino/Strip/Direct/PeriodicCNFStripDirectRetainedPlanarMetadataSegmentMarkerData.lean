/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeDrawingSegmentCount
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaShapeData

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
    {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
    {language : Input → Prop}
    (decider : PeriodicCNF.ProgramSource encoding language)
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormulaShape decider symbols).flatMap
    retainedSegmentMarkerBlock

end LeanTrominoes.PeriodicCNFStripReduction
