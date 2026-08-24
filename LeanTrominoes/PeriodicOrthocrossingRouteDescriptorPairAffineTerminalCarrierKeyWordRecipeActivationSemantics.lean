/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeLength

/-! # Semantics of compiled terminal carrier-key recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- The compiled terminal activation bits are exactly the semantic flattened
recipe activations. -/
@[simp] theorem terminalCarrierKeyExpandedActives_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalCarrierKeyExpandedActives tokens =
      expandedActives (terminalCarrierKeyActivations tokens)
        terminalCarrierKeyRecipeBlocks := by
  unfold terminalCarrierKeyExpandedActives predicateListExpandedActives
  rw [predicateListTruthValues_eq]
  change compiledExpandedActives terminalCarrierKeyRecipeBlocks
      (terminalCarrierKeyActivations tokens) = _
  rw [compiledExpandedActives_eq _ _
    (terminalCarrierKeyActivations_length tokens)]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
