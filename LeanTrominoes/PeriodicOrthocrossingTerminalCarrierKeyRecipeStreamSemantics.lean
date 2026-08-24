/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeStreamCompiler

/-! # Semantics of terminal carrier-key guarded-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalCarrierKeyRecipeStream

def guardedWords (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorPairAffine.terminalCarrierKeyGuardedWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

/-- Mapping the terminal block compiler over canonical tagged pairs emits
exactly the delimiter encoding of their concatenated guarded words. -/
@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [TerminalCarrierKeyRecipeEmitter.emittedTokens_eq_encode]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end TerminalCarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
