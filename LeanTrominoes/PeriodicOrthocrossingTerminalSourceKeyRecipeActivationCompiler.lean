/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipeData

/-! # Compiled activations for doubled terminal source-key recipes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairCarrierKeyWordRecipes

def terminalSourceKeyExpandedActives
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  predicateListExpandedActives carrierSegmentPredicates
    terminalSourceKeyRecipeBlocks tokens

noncomputable def terminalSourceKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id terminalSourceKeyExpandedActives :=
  predicateListExpandedActivesComputableInPolyTime
    carrierSegmentPredicates terminalSourceKeyRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
