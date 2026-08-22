/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairCrossingMarkerBlocks
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorWordPairData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingSemantics

/-! # Crossing semantics of direct-source descriptor word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceWordPairCrossingSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceWordPairCrossingSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The already compiled direct word-pair stream is the canonical word
encoding of the row-major descriptor square. -/
theorem directSourceRouteDescriptorWordPairs_eq_descriptorWordPairs
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorWordPairs decider symbols =
      RouteDescriptorBinaryWordPairs.descriptorWordPairs
        (numericRouteDescriptors
          (directSourceFormula decider symbols)) := by
  unfold directSourceRouteDescriptorWordPairs
    directSourceRouteDescriptorBinaryWords
  exact
    RouteDescriptorBinaryWordPairs.pairProduct_words_eq_descriptorWordPairs _

/-- Interpret the compiled descriptor-pair words as bounded crossing-marker
blocks. -/
def directSourceRouteDescriptorWordPairCrossingMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  RouteDescriptorBinaryWordPairs.crossingMarkers .variable
    (directSourceRouteDescriptorWordPairs decider symbols)

/-- The word-pair interpreter has exactly the direct semantic crossing-marker
output. -/
theorem directSourceRouteDescriptorWordPairCrossingMarkers_eq
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorWordPairCrossingMarkers decider symbols =
      directSourceRouteDescriptorCrossingMarkers decider symbols := by
  let descriptors :=
    numericRouteDescriptors (directSourceFormula decider symbols)
  unfold directSourceRouteDescriptorWordPairCrossingMarkers
  rw [directSourceRouteDescriptorWordPairs_eq_descriptorWordPairs]
  rw [RouteDescriptorBinaryWordPairs.crossingMarkers_descriptorWordPairs]
  rw [routeDescriptorPairCrossingMarkerBlocks_flatten
    FormulaShapeDirectionOrdering.Token.variable descriptors
    (numericRouteDescriptors_selfIndexed
      (directSourceFormula decider symbols))
    (numericRouteDescriptors_commonGridSize
      (directSourceFormula decider symbols)
      (directSource_incidencesWithMetadata_ne_nil decider symbols))]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
