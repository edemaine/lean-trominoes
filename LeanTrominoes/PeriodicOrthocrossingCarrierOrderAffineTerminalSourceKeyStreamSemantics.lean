/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Semantics of direction-split terminal source-component streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalSourceKeyStream

def guardedComponentWords
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorPairAffine.terminalDirectionalSourceKeyGuardedComponentWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨guardedComponentWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [TerminalDirectionalSourceKeyEmitter.emittedTokens_eq_encode]
  unfold guardedComponentWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end TerminalDirectionalSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing
