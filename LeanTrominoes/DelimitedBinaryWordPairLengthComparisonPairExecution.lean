/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonReadExecution
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonCompareExecution

/-! # One-pair execution for delimited word-length comparison -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairLengthComparisonMachine

open DelimitedBinaryWordPairs

@[simp] theorem compareFrom_equal (first : List α) (second : List β) :
    compareFrom .equal first second = compareLengths first second := by
  unfold compareFrom
  cases compareLengths first second <;> rfl

@[simp] theorem compareLengths_reverse
    (first : List α) (second : List β) :
    compareLengths first.reverse second.reverse =
      compareLengths first second := by
  simp [compareLengths]

def pairTime (first second : List Bool) : Nat :=
  1 + (first.length + 1) + (second.length + 1) +
    compareTime first.reverse second.reverse

def pair_evalsInTime (first second : List Bool) (tail : List Token)
    (resultReverse output : List LengthOrdering) :
    EvalsToInTime (TM2.step program)
      (scanCfg
        ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
      (some (scanCfg
        ⟨tail, [], [],
          compareLengths first second :: resultReverse, output⟩))
      (pairTime first second) := by
  let afterStart : TapeData :=
    ⟨first.map Token.firstBit ++
        Token.middle ::
          (second.map Token.secondBit ++ Token.pairEnd :: tail),
      [], [], resultReverse, output⟩
  let afterFirst : TapeData :=
    ⟨second.map Token.secondBit ++ Token.pairEnd :: tail,
      first.reverse, [], resultReverse, output⟩
  let afterSecond : TapeData :=
    ⟨tail, first.reverse, second.reverse, resultReverse, output⟩
  have scanned := oneStep (step_scan_pairStart
    ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩
    (first.map Token.firstBit ++
      Token.middle ::
        (second.map Token.secondBit ++ Token.pairEnd :: tail))
    (by simp [pairTokens]))
  have readFirst := readFirst_evalsInTime first
    (second.map Token.secondBit ++ Token.pairEnd :: tail) afterStart rfl
  have readSecond := readSecond_evalsInTime second tail afterFirst rfl
  have readFirst' :
      EvalsToInTime (TM2.step program) (readFirstCfg afterStart)
        (some (readSecondCfg afterFirst)) (first.length + 1) := by
    simpa [afterStart, afterFirst] using readFirst
  have readSecond' :
      EvalsToInTime (TM2.step program) (readSecondCfg afterFirst)
        (some (compareCfg .equal afterSecond)) (second.length + 1) := by
    simpa [afterFirst, afterSecond] using readSecond
  have compared := compare_evalsInTime first.reverse second.reverse .equal
    tail resultReverse output
  have firstTwo := EvalsToInTime.trans (TM2.step program)
    1 (first.length + 1)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
    (readFirstCfg afterStart)
    (some (readSecondCfg afterFirst))
    scanned readFirst'
  have firstThree := EvalsToInTime.trans (TM2.step program)
    (first.length + 2) (second.length + 1)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
    (readSecondCfg afterFirst)
    (some (compareCfg .equal afterSecond))
    firstTwo readSecond'
  have firstThree' :
      EvalsToInTime (TM2.step program)
        (scanCfg
          ⟨pairTokens (first, second) ++ tail, [], [],
            resultReverse, output⟩)
        (some (compareCfg .equal afterSecond))
        (first.length + second.length + 3) := by
    convert firstThree using 1
    omega
  have composed := EvalsToInTime.trans (TM2.step program)
    (first.length + second.length + 3)
    (compareTime first.reverse second.reverse)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
    (compareCfg .equal afterSecond)
    (some (scanCfg
      ⟨tail, [], [],
        compareFrom .equal first.reverse second.reverse :: resultReverse,
        output⟩))
    firstThree' compared
  convert composed using 1
  · simp
  · simp [pairTime]
    omega

end DelimitedBinaryWordPairLengthComparisonMachine
end LeanTrominoes
