/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductSetupSteps

/-! # Outer-word setup execution for the binary-word product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def readOuter_evalsInTime (word : List Bool) (tail : List WordToken)
    (data : TapeData)
    (outerEq : data.outer =
      word.map DelimitedBinaryWords.Token.bit ++ .wordEnd :: tail) :
    EvalsToInTime (TM2.step program) (readOuterCfg data)
      (some (reverseFirstCfg
        { data with
          outer := tail
          first := word.reverse ++ data.first }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_readOuter_wordEnd data tail outerEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData :=
        { data with
          outer := word.map DelimitedBinaryWords.Token.bit ++
            DelimitedBinaryWords.Token.wordEnd :: tail
          first := bit :: data.first }
      have first := oneStep (step_readOuter_bit data bit
        (word.map DelimitedBinaryWords.Token.bit ++
          DelimitedBinaryWords.Token.wordEnd :: tail) outerEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (readOuterCfg data) (readOuterCfg nextData)
        (some (reverseFirstCfg
          { nextData with
            outer := tail
            first := word.reverse ++ nextData.first }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def reverseFirst_evalsInTime (bits : List Bool) (data : TapeData)
    (firstEq : data.first = bits) :
    EvalsToInTime (TM2.step program) (reverseFirstCfg data)
      (some (scanInnerCfg
        { data with
          first := []
          firstOriginal := bits.reverse ++ data.firstOriginal }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := oneStep (step_reverseFirst_nil data firstEq)
      convert step using 1 <;> simp
  | cons bit bits induction =>
      let nextData :=
        { data with
          first := bits
          firstOriginal := bit :: data.firstOriginal }
      have first := oneStep
        (step_reverseFirst_cons data bit bits firstEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (reverseFirstCfg data) (reverseFirstCfg nextData)
        (some (scanInnerCfg
          { nextData with
            first := []
            firstOriginal := bits.reverse ++ nextData.firstOriginal }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
