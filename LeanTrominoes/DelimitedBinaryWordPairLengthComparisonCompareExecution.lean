/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonSteps

/-! # Comparison execution for delimited word-length comparison -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairLengthComparisonMachine

open DelimitedBinaryWordPairs

def compareTime : List Bool → List Bool → Nat
  | [], [] => 1
  | _ :: first, [] => 1 + compareTime first []
  | [], _ :: second => 1 + compareTime [] second
  | _ :: first, _ :: second => 1 + compareTime first second

def compare_evalsInTime (first second : List Bool)
    (ordering : LengthOrdering) (input : List Token)
    (resultReverse output : List LengthOrdering) :
    EvalsToInTime (TM2.step program)
      (compareCfg ordering
        ⟨input, first, second, resultReverse, output⟩)
      (some (scanCfg
        ⟨input, [], [],
          compareFrom ordering first second :: resultReverse, output⟩))
      (compareTime first second) := by
  induction first generalizing second ordering with
  | nil =>
      induction second generalizing ordering with
      | nil =>
          have step := oneStep (step_compare_nil_nil ordering
            ⟨input, [], [], resultReverse, output⟩ rfl rfl)
          convert step using 1 <;>
            simp [compareTime, compareFrom, compareLengths, compareNats]
      | cons secondBit secondTail induction =>
          let data : TapeData :=
            ⟨input, [], secondBit :: secondTail, resultReverse, output⟩
          have firstStep := oneStep
            (step_compare_nil_cons ordering secondBit data secondTail rfl rfl)
          have rest := induction .less
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (compareTime [] secondTail)
            (compareCfg ordering data)
            (compareCfg .less
              ⟨input, [], secondTail, resultReverse, output⟩)
            (some (scanCfg
              ⟨input, [], [],
                compareFrom .less [] secondTail :: resultReverse, output⟩))
            firstStep rest
          convert composed using 1
          · cases secondTail <;>
              simp [compareFrom, compareLengths, compareNats]
          · simp only [compareTime]
            omega
  | cons firstBit firstTail induction =>
      cases second with
      | nil =>
          let data : TapeData :=
            ⟨input, firstBit :: firstTail, [], resultReverse, output⟩
          have firstStep := oneStep
            (step_compare_cons_nil ordering firstBit data firstTail rfl rfl)
          have rest := induction [] .greater
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (compareTime firstTail [])
            (compareCfg ordering data)
            (compareCfg .greater
              ⟨input, firstTail, [], resultReverse, output⟩)
            (some (scanCfg
              ⟨input, [], [],
                compareFrom .greater firstTail [] :: resultReverse, output⟩))
            firstStep rest
          convert composed using 1
          · cases firstTail <;>
              simp [compareFrom, compareLengths, compareNats]
          · simp only [compareTime]
            omega
      | cons secondBit secondTail =>
          let data : TapeData :=
            ⟨input, firstBit :: firstTail, secondBit :: secondTail,
              resultReverse, output⟩
          have firstStep := oneStep
            (step_compare_cons_cons ordering firstBit secondBit data
              firstTail secondTail rfl rfl)
          have rest := induction secondTail ordering
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (compareTime firstTail secondTail)
            (compareCfg ordering data)
            (compareCfg ordering
              ⟨input, firstTail, secondTail, resultReverse, output⟩)
            (some (scanCfg
              ⟨input, [], [],
                compareFrom ordering firstTail secondTail :: resultReverse,
                output⟩))
            firstStep rest
          convert composed using 1
          · simp [compareFrom, compareLengths, compareNats]
          · simp only [compareTime]
            omega

end DelimitedBinaryWordPairLengthComparisonMachine
end LeanTrominoes
