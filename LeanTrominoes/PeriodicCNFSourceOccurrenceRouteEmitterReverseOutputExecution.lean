/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterPushOutputStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterReverseOutputSteps

/-! # Final output reversal for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def reverseTime : List OutputToken → Nat
  | [] => 1
  | _ :: tokens => reverseTime tokens + 2

theorem reverseTime_eq (tokens : List OutputToken) :
    reverseTime tokens = 2 * tokens.length + 1 := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp only [reverseTime, List.length_cons, induction]
      omega

noncomputable def reverseOutput_evalsInTime (cursor : Cursor)
    (data : TapeData) (tokens : List OutputToken)
    (outputReverseEq : data.outputReverse = tokens) :
    EvalsToInTime machine.step
      (reverseOutputCfg cursor data)
      (some (cleanupCfg .input cursor
        { data with
          outputReverse := []
          output := tokens.reverse ++ data.output }))
      (reverseTime tokens) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil cursor data outputReverseEq)
      simpa only [reverseTime, List.reverse_nil, List.nil_append]
        using step
  | cons token tokens induction =>
      let popped : TapeData := { data with outputReverse := tokens }
      let pushed : TapeData := { popped with output := token :: data.output }
      have first := oneStep
        (step_reverseOutput_cons cursor data token tokens outputReverseEq)
      have second := oneStep (step_pushOutput cursor popped token)
      have firstTwo := EvalsToInTime.trans machine.step 1 1
        (reverseOutputCfg cursor data)
        (pushOutputCfg cursor token popped)
        (some (reverseOutputCfg cursor pushed)) first second
      have pushedEq : pushed.outputReverse = tokens := by
        rfl
      have rest := induction pushed pushedEq
      have whole := EvalsToInTime.trans machine.step (1 + 1)
        (reverseTime tokens)
        (reverseOutputCfg cursor data)
        (reverseOutputCfg cursor pushed)
        (some (cleanupCfg .input cursor
          { pushed with
            outputReverse := []
            output := tokens.reverse ++ pushed.output }))
        firstTwo rest
      simpa only [popped, pushed, reverseTime, List.reverse_cons,
        List.singleton_append, List.append_assoc] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
