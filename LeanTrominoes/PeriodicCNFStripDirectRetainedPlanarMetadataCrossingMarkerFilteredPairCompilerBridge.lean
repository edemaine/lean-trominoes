/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerCompilerBridge
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerFilteredPairSemantics

/-! # Compiler bridge from filtered crossing pairs to semantic markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- A polynomial-time filtered-pair emitter implements the quadratic pair-scan
compiler boundary. -/
noncomputable def directRetainedPlanarMetadataCrossingPairMarkerCompilerOfFilteredPairs
    (filteredCompiler :
      DirectRetainedPlanarMetadataCrossingFilteredPairMarkerCompiler decider) :
    DirectRetainedPlanarMetadataCrossingPairMarkerCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCrossingFilteredPairMarkers decider)
    (directRetainedPlanarMetadataCrossingPairMarkers decider)
    (directRetainedPlanarMetadataCrossingFilteredPairMarkers_eq_pairMarkers
      decider)
    filteredCompiler

/-- A polynomial-time filtered-pair emitter therefore implements the exact
semantic crossing-marker compiler boundary. -/
noncomputable def directRetainedPlanarMetadataCrossingMarkerCompilerOfFilteredPairs
    (filteredCompiler :
      DirectRetainedPlanarMetadataCrossingFilteredPairMarkerCompiler decider) :
    DirectRetainedPlanarMetadataCrossingMarkerCompiler decider :=
  directRetainedPlanarMetadataCrossingMarkerCompilerOfPairScan decider
    (directRetainedPlanarMetadataCrossingPairMarkerCompilerOfFilteredPairs
      decider filteredCompiler)

end LeanTrominoes.PeriodicCNFStripReduction
