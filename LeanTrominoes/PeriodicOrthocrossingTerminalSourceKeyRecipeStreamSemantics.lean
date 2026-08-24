/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamData

/-! # Semantics of terminal source-key guarded-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeStream

/-- Mapping the terminal source-key block compiler over canonical tagged
pairs emits exactly the encoding of their concatenated guarded words. -/
@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [TerminalSourceKeyRecipeEmitter.emittedTokens_eq_encode]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end TerminalSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
