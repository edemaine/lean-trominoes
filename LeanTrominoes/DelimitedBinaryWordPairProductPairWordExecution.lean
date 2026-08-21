/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductPairSteps

/-! # One-word pair-emission loops for the ordered-product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def emitFirst_evalsInTime (word : List Bool) (data : TapeData)
    (firstOriginalEq : data.firstOriginal = word) :
    EvalsToInTime (TM2.step program) (emitFirstCfg data)
      (some (scanSecondCfg
        { data with
          first := word.reverse ++ data.first
          firstOriginal := []
          outputReverse :=
            DelimitedBinaryWordPairs.Token.middle ::
              (word.map
                DelimitedBinaryWordPairs.Token.firstBit).reverse ++
                data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_emitFirst_nil data firstOriginalEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData :=
        { data with
          first := bit :: data.first
          firstOriginal := word
          outputReverse :=
            DelimitedBinaryWordPairs.Token.firstBit bit ::
              data.outputReverse }
      have first := oneStep
        (step_emitFirst_cons data bit word firstOriginalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (emitFirstCfg data) (emitFirstCfg nextData)
        (some (scanSecondCfg
          { nextData with
            first := word.reverse ++ nextData.first
            firstOriginal := []
            outputReverse :=
              DelimitedBinaryWordPairs.Token.middle ::
                (word.map
                  DelimitedBinaryWordPairs.Token.firstBit).reverse ++
                  nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def scanSecond_evalsInTime (word : List Bool) (tail : List WordToken)
    (data : TapeData)
    (sourceEq : data.source =
      word.map DelimitedBinaryWords.Token.bit ++ .wordEnd :: tail) :
    EvalsToInTime (TM2.step program) (scanSecondCfg data)
      (some (restoreFirstCfg
        { data with
          source := tail
          sourceRestore :=
            (word.map DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]).reverse ++
                data.sourceRestore
          outputReverse :=
            DelimitedBinaryWordPairs.Token.pairEnd ::
              (word.map
                DelimitedBinaryWordPairs.Token.secondBit).reverse ++
                data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_scanSecond_wordEnd data tail sourceEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData :=
        { data with
          source := word.map DelimitedBinaryWords.Token.bit ++
            DelimitedBinaryWords.Token.wordEnd :: tail
          sourceRestore :=
            DelimitedBinaryWords.Token.bit bit :: data.sourceRestore
          outputReverse :=
            DelimitedBinaryWordPairs.Token.secondBit bit ::
              data.outputReverse }
      have first := oneStep (step_scanSecond_bit data bit
        (word.map DelimitedBinaryWords.Token.bit ++
          DelimitedBinaryWords.Token.wordEnd :: tail) sourceEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (scanSecondCfg data) (scanSecondCfg nextData)
        (some (restoreFirstCfg
          { nextData with
            source := tail
            sourceRestore :=
              (word.map DelimitedBinaryWords.Token.bit ++
                [DelimitedBinaryWords.Token.wordEnd]).reverse ++
                  nextData.sourceRestore
            outputReverse :=
              DelimitedBinaryWordPairs.Token.pairEnd ::
                (word.map
                  DelimitedBinaryWordPairs.Token.secondBit).reverse ++
                    nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def restoreFirst_evalsInTime (bits : List Bool) (data : TapeData)
    (firstEq : data.first = bits) :
    EvalsToInTime (TM2.step program) (restoreFirstCfg data)
      (some (scanInnerCfg
        { data with
          first := []
          firstOriginal := bits.reverse ++ data.firstOriginal }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := oneStep (step_restoreFirst_nil data firstEq)
      convert step using 1 <;> simp
  | cons bit bits induction =>
      let nextData :=
        { data with
          first := bits
          firstOriginal := bit :: data.firstOriginal }
      have first := oneStep
        (step_restoreFirst_cons data bit bits firstEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (restoreFirstCfg data) (restoreFirstCfg nextData)
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
