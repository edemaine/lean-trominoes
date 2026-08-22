/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics

/-! # Descriptor-pair crossing-marker blocks for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourcePairCrossingMarkerBlocksStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourcePairCrossingMarkerBlocksVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- One bounded marker block for every row-major ordered descriptor pair. -/
def directSourceRouteDescriptorPairCrossingMarkerBlocks
    (symbols : List encoding.Γ) :
    List (List FormulaShapeDirectionOrdering.Token) :=
  let descriptors :=
    numericRouteDescriptors (directSourceFormula decider symbols)
  routeDescriptorPairCrossingMarkerBlocksAtPeriod
    .variable (routeDescriptorStreamGridSize descriptors) descriptors

/-- The pair-major bounded blocks flatten to the exact direct crossing-marker
word used by retained planar metadata. -/
theorem directSourceRouteDescriptorCrossingMarkers_eq_pairBlocks
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorCrossingMarkers decider symbols =
      (directSourceRouteDescriptorPairCrossingMarkerBlocks
        decider symbols).flatten := by
  let descriptors :=
    numericRouteDescriptors (directSourceFormula decider symbols)
  have flattened :=
    routeDescriptorPairCrossingMarkerBlocksAtPeriod_flatten
      FormulaShapeDirectionOrdering.Token.variable
      (routeDescriptorStreamGridSize descriptors) descriptors
      (numericRouteDescriptors_selfIndexed
        (directSourceFormula decider symbols))
  unfold directSourceRouteDescriptorCrossingMarkers
    routeDescriptorOrientedCrossingCount
    routeDescriptorOrientedCrossingOccurrencePairs
    directSourceRouteDescriptorPairCrossingMarkerBlocks
  exact flattened.symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
