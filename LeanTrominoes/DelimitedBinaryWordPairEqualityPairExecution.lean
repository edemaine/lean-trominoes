/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualityReadExecution
import LeanTrominoes.DelimitedBinaryWordPairEqualityCompareExecution

/-! # One-pair execution for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

def pairTime (first second : List Bool) : Nat :=
  1 + (first.length + 1) + (second.length + 1) +
    compareTime first.reverse second.reverse

def pair_evalsInTime (first second : List Bool) (tail : List Token)
    (resultReverse output : List Bool) :
    EvalsToInTime (TM2.step program)
      (scanCfg
        ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
      (some (scanCfg
        ⟨tail, [], [], decide (first = second) :: resultReverse, output⟩))
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
        (some (compareCfg true afterSecond)) (second.length + 1) := by
    simpa [afterFirst, afterSecond] using readSecond
  have compared := compare_evalsInTime first.reverse second.reverse true
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
    (some (compareCfg true afterSecond))
    firstTwo
    readSecond'
  have firstThree' :
      EvalsToInTime (TM2.step program)
        (scanCfg
          ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
        (some (compareCfg true afterSecond))
        (first.length + second.length + 3) := by
    convert firstThree using 1
    omega
  have composed := EvalsToInTime.trans (TM2.step program)
    (first.length + second.length + 3)
    (compareTime first.reverse second.reverse)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], resultReverse, output⟩)
    (compareCfg true afterSecond)
    (some (scanCfg
      ⟨tail, [], [],
        decide (first.reverse = second.reverse) :: resultReverse,
        output⟩))
    firstThree'
    compared
  convert composed using 1
  · simp
  · simp [pairTime]
    omega

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
