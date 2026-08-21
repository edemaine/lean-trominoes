/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeData
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData

/-! # Direct retained metadata source-atom marker data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

/-- Keep one retained metadata variable marker for a formula-shape variable
token and discard clause-profile tokens. -/
def retainedAtomMarkerBlock :
    FormulaShape.Token → List FormulaShapeDirectionOrdering.Token
  | .clause _ => []
  | .variable => [.variable]

/-- Extract the source-atom portion of the retained metadata marker suffix
from the already compiled guarded formula-shape stream. -/
def directRetainedPlanarMetadataAtomMarkers
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormulaShape decider symbols).flatMap retainedAtomMarkerBlock

end LeanTrominoes.PeriodicCNFStripReduction
