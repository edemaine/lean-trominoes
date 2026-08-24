/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingTruthCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationCompiler

/-! # Compiler composition for crossing recipe activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Expand the compiled crossing truth word across fixed recipe blocks. -/
def compiledRecipeExpandedActives (blocks : List (List Recipe))
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  compiledExpandedActives blocks (truthValues tokens)

/-- Compiled crossing truth followed by fixed recipe-block expansion is
polynomial-time computable. -/
noncomputable def compiledRecipeExpandedActivesComputableInPolyTime
    (blocks : List (List Recipe)) :
    TM2ComputableInPolyTime id id
      (compiledRecipeExpandedActives blocks) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    truthValuesComputableInPolyTime
    (compiledExpandedActivesComputableInPolyTime blocks)
  unfold compiledRecipeExpandedActives
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
