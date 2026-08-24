/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueLength

/-! # Exact semantics of compiled terminal carrier-key axis fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

@[simp] theorem terminalCarrierKeyAxisCompiledFields_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalCarrierKeyAxisCompiledFields tokens =
      UnaryFieldEncoderMachine.unaryFields
        (terminalCarrierKeyAxisValues tokens) := by
  unfold terminalCarrierKeyAxisCompiledFields
    terminalCarrierKeyAxisValues
  exact FixedAxisUnaryFields.compiledFields_eq _ _
    (terminalCarrierKeyExpandedActives_axis_length tokens)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
