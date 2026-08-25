/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessDrainExecution

/-! # Cancellation execution for unary word-pair excesses -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

def cancelTime : List Bool → List Bool → Nat
  | [], [] => 1
  | _ :: first, [] => 1 + drainTime first
  | [], _ :: second => 1 + drainTime second
  | _ :: first, _ :: second => 1 + cancelTime first second

def excessUnits (keepFirst : Bool) (first second : List Bool) :
    List UnaryFieldEncoderMachine.Symbol :=
  List.replicate (excess keepFirst first second) .unit

@[simp] theorem replicate_unit_succ_append (count : Nat)
    (tail : List UnaryFieldEncoderMachine.Symbol) :
    List.replicate (count + 1) .unit ++ tail =
      List.replicate count .unit ++ .unit :: tail := by
  rw [List.replicate_add]
  simp

def cancel_evalsInTime (keepFirst : Bool) (first second : List Bool)
    (input : List DelimitedBinaryWordPairs.Token)
    (outputReverse output : List UnaryFieldEncoderMachine.Symbol) :
    EvalsToInTime (TM2.step (program keepFirst))
      (cancelCfg ⟨input, first, second, outputReverse, output⟩)
      (some (emitDelimiterCfg
        ⟨input, [], [],
          excessUnits keepFirst first second ++ outputReverse, output⟩))
      (cancelTime first second) := by
  induction first generalizing second outputReverse with
  | nil =>
      cases second with
      | nil =>
          have step := oneStep (step_cancel_nil_nil keepFirst
            ⟨input, [], [], outputReverse, output⟩ rfl rfl)
          simpa [cancelTime, excessUnits, excess] using step
      | cons secondBit secondTail =>
          have firstStep := oneStep (step_cancel_nil_cons keepFirst
            ⟨input, [], secondBit :: secondTail, outputReverse, output⟩
            secondBit secondTail rfl rfl)
          have rest := drainSecond_evalsInTime keepFirst (!keepFirst)
            secondTail input []
            (if keepFirst then outputReverse else .unit :: outputReverse)
            output
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (drainTime secondTail)
            (cancelCfg
              ⟨input, [], secondBit :: secondTail, outputReverse, output⟩)
            (drainSecondCfg (!keepFirst)
              ⟨input, [], secondTail,
                if keepFirst then outputReverse
                else .unit :: outputReverse,
                output⟩)
            (some (emitDelimiterCfg
              ⟨input, [], [],
                emittedReverse (!keepFirst) secondTail ++
                  (if keepFirst then outputReverse
                  else .unit :: outputReverse),
                output⟩))
            firstStep rest
          cases keepFirst <;>
            convert composed using 1 <;>
              simp [cancelTime, excessUnits, excess, emittedReverse] <;>
              omega
  | cons firstBit firstTail induction =>
      cases second with
      | nil =>
          have firstStep := oneStep (step_cancel_cons_nil keepFirst
            ⟨input, firstBit :: firstTail, [], outputReverse, output⟩
            firstBit firstTail rfl rfl)
          have rest := drainFirst_evalsInTime keepFirst keepFirst
            firstTail input []
            (if keepFirst then .unit :: outputReverse else outputReverse)
            output
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (drainTime firstTail)
            (cancelCfg
              ⟨input, firstBit :: firstTail, [], outputReverse, output⟩)
            (drainFirstCfg keepFirst
              ⟨input, firstTail, [],
                if keepFirst then .unit :: outputReverse else outputReverse,
                output⟩)
            (some (emitDelimiterCfg
              ⟨input, [], [],
                emittedReverse keepFirst firstTail ++
                  (if keepFirst then .unit :: outputReverse
                  else outputReverse),
                output⟩))
            firstStep rest
          cases keepFirst <;>
            convert composed using 1 <;>
              simp [cancelTime, excessUnits, excess, emittedReverse] <;>
              omega
      | cons secondBit secondTail =>
          have firstStep := oneStep (step_cancel_cons_cons keepFirst
            ⟨input, firstBit :: firstTail, secondBit :: secondTail,
              outputReverse, output⟩
            firstBit secondBit firstTail secondTail rfl rfl)
          have rest := induction secondTail outputReverse
          have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
            1 (cancelTime firstTail secondTail)
            (cancelCfg
              ⟨input, firstBit :: firstTail, secondBit :: secondTail,
                outputReverse, output⟩)
            (cancelCfg
              ⟨input, firstTail, secondTail, outputReverse, output⟩)
            (some (emitDelimiterCfg
              ⟨input, [], [],
                excessUnits keepFirst firstTail secondTail ++ outputReverse,
                output⟩))
            firstStep rest
          convert composed using 1
          · simp [excessUnits, excess]
          · simp [cancelTime, Nat.add_comm]

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
