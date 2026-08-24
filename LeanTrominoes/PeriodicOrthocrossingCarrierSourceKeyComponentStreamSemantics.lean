/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamSemanticData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCrossingTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyTerminalTokenSemantics

/-! # Semantics of the complete source-key component stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

/-- On canonical descriptor words, the combined compiler emits the exact
terminal-prefix/crossing-suffix doubled guarded-word stream. -/
@[simp] theorem tokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
  rw [tokens, terminalTokens_descriptorWords,
    crossingTokens_descriptorWords]
  simp [guardedWords, DelimitedBinaryWords.encode,
    List.flatMap_append]

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
