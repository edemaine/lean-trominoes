/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualitySteps

/-! # Word-reading executions for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

def readFirst_evalsInTime (word : List Bool) (tail : List Token)
    (data : TapeData)
    (inputEq : data.input = word.map Token.firstBit ++ .middle :: tail) :
    EvalsToInTime (TM2.step program) (readFirstCfg data)
      (some (readSecondCfg
        { data with
          input := tail
          first := word.reverse ++ data.first }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_readFirst_middle data tail inputEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData :=
        { data with
          input := word.map Token.firstBit ++ Token.middle :: tail
          first := bit :: data.first }
      have first := oneStep (step_readFirst_bit data bit
        (word.map Token.firstBit ++ .middle :: tail) inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (readFirstCfg data) (readFirstCfg nextData)
        (some (readSecondCfg
          { nextData with
            input := tail
            first := word.reverse ++ nextData.first }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def readSecond_evalsInTime (word : List Bool) (tail : List Token)
    (data : TapeData)
    (inputEq : data.input = word.map Token.secondBit ++ .pairEnd :: tail) :
    EvalsToInTime (TM2.step program) (readSecondCfg data)
      (some (compareCfg true
        { data with
          input := tail
          second := word.reverse ++ data.second }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_readSecond_pairEnd data tail inputEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData :=
        { data with
          input := word.map Token.secondBit ++ Token.pairEnd :: tail
          second := bit :: data.second }
      have first := oneStep (step_readSecond_bit data bit
        (word.map Token.secondBit ++ .pairEnd :: tail) inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (readSecondCfg data) (readSecondCfg nextData)
        (some (compareCfg true
          { nextData with
            input := tail
            second := word.reverse ++ nextData.second }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
