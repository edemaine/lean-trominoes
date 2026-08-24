/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeLength

/-! # Semantics of compiled terminal source-key recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Compiled terminal source-key activation bits are exactly the semantic
flattened recipe activations. -/
@[simp] theorem terminalSourceKeyExpandedActives_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalSourceKeyExpandedActives tokens =
      expandedActives
        (carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens tokens)
        terminalSourceKeyRecipeBlocks := by
  unfold terminalSourceKeyExpandedActives predicateListExpandedActives
  rw [predicateListTruthValues_eq]
  apply compiledExpandedActives_eq
  rw [List.length_map]
  exact terminalSourceKeyRecipeBlocks_length.symm

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
