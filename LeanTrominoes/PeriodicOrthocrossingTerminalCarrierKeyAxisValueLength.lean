/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueData

/-! # Alignment lengths of padded terminal axis values -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- The fixed axis word has exactly one bit per flattened terminal recipe. -/
theorem terminalCarrierKeyRecipeAxes_length :
    terminalCarrierKeyRecipeAxes.length =
      terminalCarrierKeyRecipeBlocks.flatten.length := by
  unfold terminalCarrierKeyRecipeAxes
  exact AlternatingBlockAxes.axes_length terminalCarrierKeyRecipeBlocks

/-- Every runtime terminal activation word aligns with the fixed axis word. -/
theorem terminalCarrierKeyExpandedActives_axis_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (terminalCarrierKeyExpandedActives tokens).length =
      terminalCarrierKeyRecipeAxes.length := by
  rw [terminalCarrierKeyExpandedActives_eq,
    expandedActives_length_of_length_eq]
  · exact terminalCarrierKeyRecipeAxes_length.symm
  · exact terminalCarrierKeyActivations_length tokens

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
