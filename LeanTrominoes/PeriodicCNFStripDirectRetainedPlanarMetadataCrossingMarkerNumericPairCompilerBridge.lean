/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerNumericPairSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerOccurrencePairCompilerBridge

/-! # Compiler bridge from numeric crossing pairs to semantic markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedNumericCrossingPairCompilerBridgeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A numeric route/segment pair emitter supplies the direct occurrence-pair
compiler boundary. -/
noncomputable def directRetainedPlanarMetadataCrossingOccurrencePairMarkerCompilerOfNumericPairs
    (numericCompiler :
      DirectRetainedPlanarMetadataCrossingNumericPairMarkerCompiler decider) :
    DirectRetainedPlanarMetadataCrossingOccurrencePairMarkerCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataCrossingNumericPairMarkers decider)
    (directRetainedPlanarMetadataCrossingOccurrencePairMarkers decider)
    (directRetainedPlanarMetadataCrossingNumericPairMarkers_eq_occurrencePairMarkers
      decider)
    numericCompiler

/-- Consequently, a numeric route/segment pair emitter supplies the exact
semantic crossing-marker compiler. -/
noncomputable def directRetainedPlanarMetadataCrossingMarkerCompilerOfNumericPairs
    (numericCompiler :
      DirectRetainedPlanarMetadataCrossingNumericPairMarkerCompiler decider) :
    DirectRetainedPlanarMetadataCrossingMarkerCompiler decider :=
  directRetainedPlanarMetadataCrossingMarkerCompilerOfOccurrencePairs decider
    (directRetainedPlanarMetadataCrossingOccurrencePairMarkerCompilerOfNumericPairs
      decider numericCompiler)

end LeanTrominoes.PeriodicCNFStripReduction
