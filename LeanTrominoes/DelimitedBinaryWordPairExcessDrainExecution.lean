/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessMachineSteps

/-! # Remainder-draining executions for unary word-pair excesses -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

def drainTime (word : List Bool) : Nat := word.length + 1

def emittedReverse (emit : Bool) (word : List Bool) :
    List UnaryFieldEncoderMachine.Symbol :=
  if emit then (word.map fun _ => .unit).reverse else []

def drainFirst_evalsInTime (keepFirst emit : Bool) (word : List Bool)
    (input : List DelimitedBinaryWordPairs.Token) (second : List Bool)
    (outputReverse output : List UnaryFieldEncoderMachine.Symbol) :
    EvalsToInTime (TM2.step (program keepFirst))
      (drainFirstCfg emit
        ⟨input, word, second, outputReverse, output⟩)
      (some (emitDelimiterCfg
        ⟨input, [], second,
          emittedReverse emit word ++ outputReverse, output⟩))
      (drainTime word) := by
  cases emit with
  | false =>
      induction word generalizing outputReverse with
      | nil =>
          have step := oneStep (step_drainFirst_nil keepFirst false
            ⟨input, [], second, outputReverse, output⟩ rfl)
          simpa [drainTime, emittedReverse] using step
      | cons bit tail induction =>
          have first := oneStep (step_drainFirst_cons keepFirst false
            ⟨input, bit :: tail, second, outputReverse, output⟩ bit tail rfl)
          have rest := induction outputReverse
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (drainTime tail)
            (drainFirstCfg false
              ⟨input, bit :: tail, second, outputReverse, output⟩)
            (drainFirstCfg false
              ⟨input, tail, second, outputReverse, output⟩)
            (some (emitDelimiterCfg
              ⟨input, [], second,
                emittedReverse false tail ++ outputReverse, output⟩))
            first rest
          simpa [drainTime, emittedReverse] using composed
  | true =>
      induction word generalizing outputReverse with
      | nil =>
          have step := oneStep (step_drainFirst_nil keepFirst true
            ⟨input, [], second, outputReverse, output⟩ rfl)
          simpa [drainTime, emittedReverse] using step
      | cons bit tail induction =>
          have first := oneStep (step_drainFirst_cons keepFirst true
            ⟨input, bit :: tail, second, outputReverse, output⟩ bit tail rfl)
          have rest := induction (.unit :: outputReverse)
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (drainTime tail)
            (drainFirstCfg true
              ⟨input, bit :: tail, second, outputReverse, output⟩)
            (drainFirstCfg true
              ⟨input, tail, second, .unit :: outputReverse, output⟩)
            (some (emitDelimiterCfg
              ⟨input, [], second,
                emittedReverse true tail ++ .unit :: outputReverse, output⟩))
            first rest
          convert composed using 1
          · simp [emittedReverse, List.reverse_cons, List.append_assoc]
          · simp [drainTime]

def drainSecond_evalsInTime (keepFirst emit : Bool) (word : List Bool)
    (input : List DelimitedBinaryWordPairs.Token) (first : List Bool)
    (outputReverse output : List UnaryFieldEncoderMachine.Symbol) :
    EvalsToInTime (TM2.step (program keepFirst))
      (drainSecondCfg emit
        ⟨input, first, word, outputReverse, output⟩)
      (some (emitDelimiterCfg
        ⟨input, first, [],
          emittedReverse emit word ++ outputReverse, output⟩))
      (drainTime word) := by
  cases emit with
  | false =>
      induction word generalizing outputReverse with
      | nil =>
          have step := oneStep (step_drainSecond_nil keepFirst false
            ⟨input, first, [], outputReverse, output⟩ rfl)
          simpa [drainTime, emittedReverse] using step
      | cons bit tail induction =>
          have firstStep := oneStep (step_drainSecond_cons keepFirst false
            ⟨input, first, bit :: tail, outputReverse, output⟩ bit tail rfl)
          have rest := induction outputReverse
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (drainTime tail)
            (drainSecondCfg false
              ⟨input, first, bit :: tail, outputReverse, output⟩)
            (drainSecondCfg false
              ⟨input, first, tail, outputReverse, output⟩)
            (some (emitDelimiterCfg
              ⟨input, first, [],
                emittedReverse false tail ++ outputReverse, output⟩))
            firstStep rest
          simpa [drainTime, emittedReverse] using composed
  | true =>
      induction word generalizing outputReverse with
      | nil =>
          have step := oneStep (step_drainSecond_nil keepFirst true
            ⟨input, first, [], outputReverse, output⟩ rfl)
          simpa [drainTime, emittedReverse] using step
      | cons bit tail induction =>
          have firstStep := oneStep (step_drainSecond_cons keepFirst true
            ⟨input, first, bit :: tail, outputReverse, output⟩ bit tail rfl)
          have rest := induction (.unit :: outputReverse)
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (drainTime tail)
            (drainSecondCfg true
              ⟨input, first, bit :: tail, outputReverse, output⟩)
            (drainSecondCfg true
              ⟨input, first, tail, .unit :: outputReverse, output⟩)
            (some (emitDelimiterCfg
              ⟨input, first, [],
                emittedReverse true tail ++ .unit :: outputReverse, output⟩))
            firstStep rest
          convert composed using 1
          · simp [emittedReverse, List.reverse_cons, List.append_assoc]
          · simp [drainTime]

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
