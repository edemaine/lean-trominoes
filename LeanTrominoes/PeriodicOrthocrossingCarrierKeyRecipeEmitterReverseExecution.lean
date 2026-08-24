/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterReverseSteps

/-! # Complete output reversal of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def reverseOutput_evalsInTime (recipes : List Recipe)
    (state : State recipes.length)
    (word : List DelimitedBinaryWords.Token) (data : TapeData)
    (outputReverseEq : data.outputReverse = word)
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (reverseOutputCfg state data)
      (some (haltDataCfg (initialState recipes.length)
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil recipes state data outputReverseEq payloadEq)
      convert step using 1 <;> simp
  | cons token word induction =>
      let nextData : TapeData :=
        { data with
          outputReverse := word
          output := token :: data.output }
      have first := oneStep
        (step_reverseOutput_cons recipes state data token word
          outputReverseEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (reverseOutputCfg state data) (reverseOutputCfg state nextData)
        (some (haltDataCfg (initialState recipes.length)
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
