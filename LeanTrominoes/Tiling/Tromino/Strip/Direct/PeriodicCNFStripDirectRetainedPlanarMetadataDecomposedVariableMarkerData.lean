/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerData

/-! # Three-family decomposition of direct retained variable markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Already compiled segment/atom markers followed by the exact crossing
marker suffix. -/
def directRetainedPlanarMetadataDecomposedVariableMarkers
    {Input : Type}
    {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
    {language : Input → Prop}
    (decider : PeriodicCNF.ProgramSource encoding language)
    (symbols : List encoding.Γ) :=
  directRetainedPlanarMetadataSegmentAtomMarkers decider symbols ++
    directRetainedPlanarMetadataCrossingMarkers decider symbols

end LeanTrominoes.PeriodicCNFStripReduction
