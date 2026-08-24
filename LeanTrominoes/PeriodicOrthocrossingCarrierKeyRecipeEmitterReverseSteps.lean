/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterStepBasics

/-! # Output-reversal steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem step_reverseOutput_nil (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (outputReverseEq : data.outputReverse = [])
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (reverseOutputCfg state data) =
      some (haltDataCfg (initialState recipes.length)
        { data with outputReverse := [] }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change outputReverse = [] at outputReverseEq
  change payload = none at payloadEq
  subst outputReverse
  subst payload
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes,
    readOutput, clearPayload, payloadPresent]

theorem step_reverseOutput_cons (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (token : DelimitedBinaryWords.Token)
    (tail : List DelimitedBinaryWords.Token)
    (outputReverseEq : data.outputReverse = token :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (reverseOutputCfg state data) =
      some (reverseOutputCfg state
        { data with
          outputReverse := tail
          output := token :: data.output }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change outputReverse = token :: tail at outputReverseEq
  change payload = none at payloadEq
  subst outputReverse
  subst payload
  cases token <;>
    simp [TM2.step, program, reverseOutputCfg, cfg, tapes,
      readOutput, outputFromState, clearPayload, payloadPresent]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
