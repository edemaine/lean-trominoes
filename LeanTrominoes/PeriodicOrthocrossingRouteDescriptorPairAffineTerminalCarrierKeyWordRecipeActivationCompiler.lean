/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeData

/-! # Compiler for terminal carrier-key recipe activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairCarrierKeyWordRecipes

/-- Compiled activation bit for every flattened terminal carrier-key recipe. -/
def terminalCarrierKeyExpandedActives
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  predicateListExpandedActives carrierSegmentPredicates
    terminalCarrierKeyRecipeBlocks tokens

/-- The fixed terminal recipe activation word is polynomial-time
computable. -/
noncomputable def terminalCarrierKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id terminalCarrierKeyExpandedActives := by
  exact predicateListExpandedActivesComputableInPolyTime
    carrierSegmentPredicates terminalCarrierKeyRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
