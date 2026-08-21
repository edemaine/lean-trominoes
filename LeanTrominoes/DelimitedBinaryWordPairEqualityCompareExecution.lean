/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualitySteps

/-! # Comparison execution for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

def compareTime : List Bool → List Bool → Nat
  | [], [] => 1
  | _ :: first, [] => 1 + compareTime first []
  | [], _ :: second => 1 + compareTime [] second
  | _ :: first, _ :: second => 1 + compareTime first second

def compare_evalsInTime (first second : List Bool) (equal : Bool)
    (input : List Token) (resultReverse output : List Bool) :
    EvalsToInTime (TM2.step program)
      (compareCfg equal ⟨input, first, second, resultReverse, output⟩)
      (some (scanCfg
        ⟨input, [], [],
          (equal && decide (first = second)) :: resultReverse, output⟩))
      (compareTime first second) := by
  induction first generalizing second equal with
  | nil =>
      induction second generalizing equal with
      | nil =>
          have step := oneStep (step_compare_nil_nil equal
            ⟨input, [], [], resultReverse, output⟩ rfl rfl)
          convert step using 1 <;> simp [compareTime]
      | cons secondBit secondTail induction =>
          let data : TapeData :=
            ⟨input, [], secondBit :: secondTail, resultReverse, output⟩
          have firstStep := oneStep
            (step_compare_nil_cons equal secondBit data secondTail rfl rfl)
          have rest := induction false
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (compareTime [] secondTail)
            (compareCfg equal data)
            (compareCfg false
              ⟨input, [], secondTail, resultReverse, output⟩)
            (some (scanCfg
              ⟨input, [], [], false :: resultReverse, output⟩))
            firstStep rest
          convert composed using 1
          · simp
          · simp only [compareTime]
            omega
  | cons firstBit firstTail induction =>
      cases second with
      | nil =>
          let data : TapeData :=
            ⟨input, firstBit :: firstTail, [], resultReverse, output⟩
          have firstStep := oneStep
            (step_compare_cons_nil equal firstBit data firstTail rfl rfl)
          have rest := induction [] false
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (compareTime firstTail [])
            (compareCfg equal data)
            (compareCfg false
              ⟨input, firstTail, [], resultReverse, output⟩)
            (some (scanCfg
              ⟨input, [], [], false :: resultReverse, output⟩))
            firstStep rest
          convert composed using 1
          · simp
          · simp only [compareTime]
            omega
      | cons secondBit secondTail =>
          let data : TapeData :=
            ⟨input, firstBit :: firstTail, secondBit :: secondTail,
              resultReverse, output⟩
          let nextEqual := equal && decide (firstBit = secondBit)
          have firstStep := oneStep
            (step_compare_cons_cons equal firstBit secondBit data
              firstTail secondTail rfl rfl)
          have rest := induction secondTail nextEqual
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (compareTime firstTail secondTail)
            (compareCfg equal data)
            (compareCfg nextEqual
              ⟨input, firstTail, secondTail, resultReverse, output⟩)
            (some (scanCfg
              ⟨input, [], [],
                (nextEqual && decide (firstTail = secondTail)) ::
                  resultReverse,
                output⟩))
            firstStep rest
          convert composed using 1
          · simp [nextEqual, Bool.and_assoc]
          · simp only [compareTime]
            omega

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
