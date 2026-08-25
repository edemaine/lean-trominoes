/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical semantics of terminal order-coordinate field streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalOrderFieldStream

@[simp] theorem emittedFields_encodeDescriptorPairs
    (keepPositive : Bool)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedFields keepPositive
        (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorPairAffine.terminalDirectionalOrderFields
            keepPositive
            (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) := by
  unfold emittedFields
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [blockFields]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end TerminalDirectionalOrderFieldStream
end LeanTrominoes.PeriodicOrthocrossing
