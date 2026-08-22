/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductMachine
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordDecoder
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData

/-! # Crossing markers interpreted from binary descriptor-word pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWordPairs

/-- Canonical binary words for the row-major ordered square of a descriptor
list. -/
def descriptorWordPairs (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordPairs.Input :=
  ⟨(descriptors ×ˢ descriptors).map fun pair =>
    (RouteDescriptorBinaryWords.descriptorWord pair.1,
      RouteDescriptorBinaryWords.descriptorWord pair.2)⟩

/-- Decode one word pair and emit its bounded self-period crossing block.
Malformed pairs contribute no markers. -/
def wordPairCrossingMarkers
    (marker : α) (pair : List Bool × List Bool) : List α :=
  match RouteDescriptorBinaryWords.decodePair pair with
  | some descriptors =>
      routeDescriptorPairCrossingMarkers marker descriptors
  | none => []

/-- Flatten all pair-local crossing-marker blocks. -/
def crossingMarkers
    (marker : α) (input : DelimitedBinaryWordPairs.Input) : List α :=
  (input.pairs.map (wordPairCrossingMarkers marker)).flatten

end RouteDescriptorBinaryWordPairs
end PeriodicOrthocrossing
end LeanTrominoes
