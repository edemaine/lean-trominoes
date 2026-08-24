/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueLength

/-! # Exact semantics of compiled crossing carrier-key axis fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

@[simp] theorem crossingCarrierKeyAxisCompiledFields_eq
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    crossingCarrierKeyAxisCompiledFields tokens =
      UnaryFieldEncoderMachine.unaryFields
        (crossingCarrierKeyAxisValues tokens) := by
  unfold crossingCarrierKeyAxisCompiledFields
    crossingCarrierKeyAxisValues
  exact FixedAxisUnaryFields.compiledFields_eq _ _
    (crossingCarrierKeyExpandedActives_axis_length tokens)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
