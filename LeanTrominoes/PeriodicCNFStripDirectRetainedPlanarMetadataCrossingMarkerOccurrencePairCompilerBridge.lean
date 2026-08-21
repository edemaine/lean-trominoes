/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerFilteredPairCompilerBridge
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerOccurrencePairSemantics

/-! # Compiler bridge from direct occurrence pairs to semantic markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossingOccurrencePairCompilerBridgeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A direct accepted-occurrence-pair emitter implements the filtered-pair
compiler boundary. -/
noncomputable def directRetainedPlanarMetadataCrossingFilteredPairMarkerCompilerOfOccurrencePairs
    (occurrencePairCompiler :
      DirectRetainedPlanarMetadataCrossingOccurrencePairMarkerCompiler
        decider) :
    DirectRetainedPlanarMetadataCrossingFilteredPairMarkerCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCrossingOccurrencePairMarkers decider)
    (directRetainedPlanarMetadataCrossingFilteredPairMarkers decider)
    (directRetainedPlanarMetadataCrossingOccurrencePairMarkers_eq_filteredPairMarkers
      decider)
    occurrencePairCompiler

/-- A direct accepted-occurrence-pair emitter therefore implements the exact
semantic crossing-marker compiler boundary. -/
noncomputable def directRetainedPlanarMetadataCrossingMarkerCompilerOfOccurrencePairs
    (occurrencePairCompiler :
      DirectRetainedPlanarMetadataCrossingOccurrencePairMarkerCompiler
        decider) :
    DirectRetainedPlanarMetadataCrossingMarkerCompiler decider :=
  directRetainedPlanarMetadataCrossingMarkerCompilerOfFilteredPairs decider
    (directRetainedPlanarMetadataCrossingFilteredPairMarkerCompilerOfOccurrencePairs
      decider occurrencePairCompiler)

end LeanTrominoes.PeriodicCNFStripReduction
