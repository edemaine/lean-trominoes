/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeStreamCompiler

/-! # Semantics of activity-supported terminal key streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalActiveCarrierKeyRecipeStream

def guardedWords (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorPairAffine.terminalActiveCarrierKeyGuardedWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [TerminalActiveCarrierKeyRecipeEmitter.emittedTokens_eq_encode]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end TerminalActiveCarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
