/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessPairExecution

/-! # Pair-list execution for unary word-pair excesses -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

def pairsTime : List (List Bool × List Bool) → Nat
  | [] => 1
  | pair :: pairs => pairTime pair.1 pair.2 + pairsTime pairs

def pairExcesses (keepFirst : Bool)
    (pairs : List (List Bool × List Bool)) : List Nat :=
  pairs.map fun pair => excess keepFirst pair.1 pair.2

@[simp] theorem excess_reverse (keepFirst : Bool)
    (first second : List Bool) :
    excess keepFirst first.reverse second.reverse =
      excess keepFirst first second := by
  simp [excess]

@[simp] theorem reverse_unaryField (number : Nat) :
    (UnaryFieldEncoderMachine.unaryField number).reverse =
      .delimiter :: List.replicate number .unit := by
  simp [UnaryFieldEncoderMachine.unaryField, List.reverse_append]

def pairs_evalsInTime (keepFirst : Bool)
    (pairs : List (List Bool × List Bool))
    (outputReverse output : List UnaryFieldEncoderMachine.Symbol) :
    EvalsToInTime (TM2.step (program keepFirst))
      (scanCfg
        ⟨pairs.flatMap pairTokens, [], [], outputReverse, output⟩)
      (some (reverseOutputCfg
        ⟨[], [], [],
          (UnaryFieldEncoderMachine.unaryFields
            (pairExcesses keepFirst pairs)).reverse ++ outputReverse,
          output⟩))
      (pairsTime pairs) := by
  induction pairs generalizing outputReverse with
  | nil =>
      have step := oneStep (step_scan_nil keepFirst
        ⟨[], [], [], outputReverse, output⟩ rfl)
      simpa [pairsTime, pairExcesses] using step
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      have pairRun := pair_evalsInTime keepFirst first second
        (pairs.flatMap pairTokens) outputReverse output
      have rest := induction
        (.delimiter :: excessUnits keepFirst first.reverse second.reverse ++
          outputReverse)
      have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
        (pairTime first second) (pairsTime pairs)
        (scanCfg
          ⟨pairTokens (first, second) ++ pairs.flatMap pairTokens,
            [], [], outputReverse, output⟩)
        (scanCfg
          ⟨pairs.flatMap pairTokens, [], [],
            .delimiter ::
              excessUnits keepFirst first.reverse second.reverse ++
                outputReverse,
            output⟩)
        (some (reverseOutputCfg
          ⟨[], [], [],
            (UnaryFieldEncoderMachine.unaryFields
              (pairExcesses keepFirst pairs)).reverse ++
                (.delimiter ::
                  excessUnits keepFirst first.reverse second.reverse ++
                    outputReverse),
            output⟩))
        pairRun rest
      have outputReverseEq :
          (UnaryFieldEncoderMachine.unaryFields
              (pairExcesses keepFirst ((first, second) :: pairs))).reverse ++
            outputReverse =
          (UnaryFieldEncoderMachine.unaryFields
              (pairExcesses keepFirst pairs)).reverse ++
            (.delimiter ::
              excessUnits keepFirst first.reverse second.reverse ++
                outputReverse) := by
        rw [show pairExcesses keepFirst ((first, second) :: pairs) =
            excess keepFirst first second :: pairExcesses keepFirst pairs by
          rfl]
        rw [UnaryFieldEncoderMachine.unaryFields_cons,
          List.reverse_append, reverse_unaryField]
        unfold excessUnits
        rw [excess_reverse]
        simp [List.append_assoc]
      convert composed using 1
      · rfl
      · rw [outputReverseEq]
      · simp only [pairsTime]
        omega

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
