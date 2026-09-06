/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterConfigurations

/-! # Basic steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem stepAux_pushTokens {recipes : List Recipe}
    (tokens : List DelimitedBinaryWords.Token)
    (next : TM2.Stmt Alphabet (Label recipes) (State recipes.length))
    (state : State recipes.length) (data : TapeData) :
    TM2.stepAux (pushTokens tokens next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          outputReverse := tokens.reverse ++ data.outputReverse }) := by
  induction tokens generalizing data with
  | nil => simp [pushTokens]
  | cons token tokens induction =>
      simp only [pushTokens, List.foldr_cons, TM2.stepAux]
      rw [update_tapes_outputReverse]
      change TM2.stepAux (pushTokens tokens next) state
          (tapes { data with
            outputReverse := token :: data.outputReverse }) = _
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
