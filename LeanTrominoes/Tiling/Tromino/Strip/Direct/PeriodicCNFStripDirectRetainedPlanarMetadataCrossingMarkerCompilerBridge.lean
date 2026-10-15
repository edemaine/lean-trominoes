/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerPairSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Compiler bridge from crossing pairs to semantic markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Any polynomial-time quadratic pair-scan emitter therefore implements the
exact semantic crossing-marker compiler boundary. -/
noncomputable def directRetainedPlanarMetadataCrossingMarkerCompilerOfPairScan
    (pairCompiler :
      DirectRetainedPlanarMetadataCrossingPairMarkerCompiler decider) :
    DirectRetainedPlanarMetadataCrossingMarkerCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCrossingPairMarkers decider)
    (directRetainedPlanarMetadataCrossingMarkers decider)
    (directRetainedPlanarMetadataCrossingPairMarkers_eq_crossingMarkers
      decider)
    pairCompiler

end LeanTrominoes.PeriodicCNFStripReduction
