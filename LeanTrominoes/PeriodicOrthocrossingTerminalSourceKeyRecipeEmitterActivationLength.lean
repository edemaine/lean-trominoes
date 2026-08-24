/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterCompiler

/-! # Activation length of terminal source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem expandedActives_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (RouteDescriptorPairAffine.terminalSourceKeyExpandedActives tokens).length =
      recipes.length := by
  rw [RouteDescriptorPairAffine.terminalSourceKeyExpandedActives_eq]
  unfold recipes
  apply expandedActives_length_of_length_eq
  rw [List.length_map]
  exact RouteDescriptorPairAffine.terminalSourceKeyRecipeBlocks_length.symm

end TerminalSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
