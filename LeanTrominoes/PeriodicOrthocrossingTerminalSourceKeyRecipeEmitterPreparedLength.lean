/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterActivationLength

/-! # Prepared-input length of terminal source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeEmitter

@[simp] theorem preparedInput_activationBits
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (CarrierKeyRecipeEmitter.activationBits (preparedInput tokens)).length =
      recipes.length := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.activationBits_prepared]
  exact expandedActives_length tokens

end TerminalSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
