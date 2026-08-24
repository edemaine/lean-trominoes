/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyTerminalTagSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamSemantics

/-! # Canonical terminal tokens of the source-key component stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

@[simp] theorem terminalTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨TerminalSourceKeyRecipeStream.guardedWords
          (descriptors ×ˢ descriptors)⟩ := by
  unfold terminalTokens
  rw [terminalTags_descriptorWords,
    TerminalSourceKeyRecipeStream.emittedStream_encodeDescriptorPairs]

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
