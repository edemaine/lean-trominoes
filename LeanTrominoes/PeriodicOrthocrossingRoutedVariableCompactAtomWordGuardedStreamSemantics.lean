/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordGuardedStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Semantics of guarded routed-variable compact atom-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordGuardedStream

def guardedWords (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorPairAffine.routedVariableCompactAtomGuardedWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [RoutedVariableCompactAtomWordEmitter.emittedTokens_eq_encode]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end RoutedVariableCompactAtomWordGuardedStream
end LeanTrominoes.PeriodicOrthocrossing
