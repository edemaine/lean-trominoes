/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueCompilerSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical semantics of terminal carrier-key axis streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalCarrierKeyAxisStream

@[simp] theorem emittedFields_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedFields (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorPairAffine.terminalCarrierKeyAxisValues
            (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) := by
  unfold emittedFields
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [RouteDescriptorPairAffine.terminalCarrierKeyAxisCompiledFields_eq]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end TerminalCarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing
