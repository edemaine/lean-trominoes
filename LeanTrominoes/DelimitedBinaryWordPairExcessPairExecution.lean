/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessReadExecution
import LeanTrominoes.DelimitedBinaryWordPairExcessCancelExecution

/-! # One-pair execution for unary word-pair excesses -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

def pairTime (first second : List Bool) : Nat :=
  1 + (first.length + 1) + (second.length + 1) +
    cancelTime first.reverse second.reverse + 1

def pair_evalsInTime (keepFirst : Bool) (first second : List Bool)
    (tail : List Token)
    (outputReverse output : List UnaryFieldEncoderMachine.Symbol) :
    EvalsToInTime (TM2.step (program keepFirst))
      (scanCfg
        ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩)
      (some (scanCfg
        ⟨tail, [], [],
          .delimiter :: excessUnits keepFirst first.reverse second.reverse ++
            outputReverse,
          output⟩))
      (pairTime first second) := by
  let afterStart : TapeData :=
    ⟨first.map Token.firstBit ++
        Token.middle ::
          (second.map Token.secondBit ++ Token.pairEnd :: tail),
      [], [], outputReverse, output⟩
  let afterFirst : TapeData :=
    ⟨second.map Token.secondBit ++ Token.pairEnd :: tail,
      first.reverse, [], outputReverse, output⟩
  let afterSecond : TapeData :=
    ⟨tail, first.reverse, second.reverse, outputReverse, output⟩
  let afterCancel : TapeData :=
    ⟨tail, [], [],
      excessUnits keepFirst first.reverse second.reverse ++ outputReverse,
      output⟩
  have scanned := oneStep (step_scan_pairStart keepFirst
    ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩
    (first.map Token.firstBit ++
      Token.middle ::
        (second.map Token.secondBit ++ Token.pairEnd :: tail))
    (by simp [pairTokens]))
  have readFirst := readFirst_evalsInTime keepFirst first
    (second.map Token.secondBit ++ Token.pairEnd :: tail) afterStart rfl
  have readSecond := readSecond_evalsInTime keepFirst second tail afterFirst rfl
  have readFirst' :
      EvalsToInTime (TM2.step (program keepFirst)) (readFirstCfg afterStart)
        (some (readSecondCfg afterFirst)) (first.length + 1) := by
    simpa [afterStart, afterFirst] using readFirst
  have readSecond' :
      EvalsToInTime (TM2.step (program keepFirst)) (readSecondCfg afterFirst)
        (some (cancelCfg afterSecond)) (second.length + 1) := by
    simpa [afterFirst, afterSecond] using readSecond
  have cancelled := cancel_evalsInTime keepFirst first.reverse second.reverse
    tail outputReverse output
  have cancelled' :
      EvalsToInTime (TM2.step (program keepFirst)) (cancelCfg afterSecond)
        (some (emitDelimiterCfg afterCancel))
        (cancelTime first.reverse second.reverse) := by
    simpa [afterSecond, afterCancel] using cancelled
  have emitted := oneStep (step_emitDelimiter keepFirst afterCancel)
  have firstTwo := EvalsToInTime.trans (TM2.step (program keepFirst))
    1 (first.length + 1)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩)
    (readFirstCfg afterStart)
    (some (readSecondCfg afterFirst))
    scanned readFirst'
  have firstThree := EvalsToInTime.trans (TM2.step (program keepFirst))
    (first.length + 2) (second.length + 1)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩)
    (readSecondCfg afterFirst)
    (some (cancelCfg afterSecond))
    firstTwo readSecond'
  have firstThree' :
      EvalsToInTime (TM2.step (program keepFirst))
        (scanCfg
          ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩)
        (some (cancelCfg afterSecond))
        (first.length + second.length + 3) := by
    convert firstThree using 1
    omega
  have firstFour := EvalsToInTime.trans (TM2.step (program keepFirst))
    (first.length + second.length + 3)
    (cancelTime first.reverse second.reverse)
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩)
    (cancelCfg afterSecond)
    (some (emitDelimiterCfg afterCancel))
    firstThree' cancelled'
  have whole := EvalsToInTime.trans (TM2.step (program keepFirst))
    (cancelTime first.reverse second.reverse +
      (first.length + second.length + 3))
    1
    (scanCfg
      ⟨pairTokens (first, second) ++ tail, [], [], outputReverse, output⟩)
    (emitDelimiterCfg afterCancel)
    (some (scanCfg
      ⟨tail, [], [],
        .delimiter :: excessUnits keepFirst first.reverse second.reverse ++
          outputReverse,
        output⟩))
    firstFour emitted
  convert whole using 1
  simp [pairTime]
  omega

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
