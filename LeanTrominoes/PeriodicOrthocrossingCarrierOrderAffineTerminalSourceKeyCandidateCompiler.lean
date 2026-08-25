/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateRecipeActivationCompiler

/-! # Compiled activations for direction-split terminal source identities -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing

/-- One activity bit for every doubled compact source-key component recipe. -/
def terminalDirectionalSourceKeyExpandedActives
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  predicateListExpandedActives terminalDirectionalPredicates
    terminalDirectionalSourceKeyRecipeBlocks tokens

def terminalDirectionalSourceKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      terminalDirectionalSourceKeyExpandedActives := by
  exact predicateListExpandedActivesComputableInPolyTime
    terminalDirectionalPredicates
    terminalDirectionalSourceKeyRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
