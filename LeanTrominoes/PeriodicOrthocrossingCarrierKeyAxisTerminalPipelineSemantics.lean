/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisTerminalPipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisTerminalTagSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisStreamSemantics

/-! # Exact terminal carrier-key axis pipeline semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisTerminalPipeline

@[simp] theorem fields_descriptorWords
    (descriptors : List RouteDescriptor) :
    fields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (CarrierKeyAxisStream.terminalValues descriptors) := by
  unfold fields CarrierKeyAxisStream.terminalValues
  rw [CarrierKeyAxisTerminalTags.tags_descriptorWords,
    TerminalCarrierKeyAxisStream.emittedFields_encodeDescriptorPairs]

end CarrierKeyAxisTerminalPipeline
end LeanTrominoes.PeriodicOrthocrossing
