/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyGuardedWordData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterPreparedLength

/-! # Semantic output of terminal source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

theorem output_eq (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.output recipes (preparedInput tokens) =
      ⟨RouteDescriptorPairAffine.terminalSourceKeyGuardedWords tokens⟩ := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorPairAffine.terminalSourceKeyExpandedActives_eq]
  have wordsEq :
      flattenedWords tokens
          (RouteDescriptorPairAffine.carrierSegmentPredicates.map fun predicate =>
            predicate.evalTokens tokens)
          RouteDescriptorPairAffine.terminalSourceKeyRecipeBlocks =
        RouteDescriptorPairAffine.terminalSourceKeyGuardedWords tokens := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg (fun words => DelimitedBinaryWords.Input.mk words) wordsEq

end TerminalSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
