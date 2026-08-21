/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductOuterRowExecution

/-! # All rows of the binary-word ordered product -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def productTokens (firsts seconds : List (List Bool)) :
    List PairToken :=
  firsts.flatMap fun first => rowTokens first seconds

def outerRowsTime (seconds : List (List Bool)) :
    List (List Bool) → Nat
  | [] => 0
  | first :: firsts =>
      outerRowTime first seconds + outerRowsTime seconds firsts

def outerRows_evalsInTime (firsts : List (List Bool))
    (outerTail : List WordToken) (seconds : List (List Bool))
    (data : TapeData)
    (outerEq : data.outer =
      firsts.flatMap DelimitedBinaryWords.wordTokens ++ outerTail)
    (sourceEq : data.source =
      seconds.flatMap DelimitedBinaryWords.wordTokens)
    (firstEq : data.first = [])
    (firstOriginalEq : data.firstOriginal = [])
    (sourceRestoreEq : data.sourceRestore = []) :
    EvalsToInTime (TM2.step program) (scanOuterCfg data)
      (some (scanOuterCfg
        { data with
          outer := outerTail
          source := seconds.flatMap DelimitedBinaryWords.wordTokens
          first := []
          firstOriginal := []
          sourceRestore := []
          outputReverse :=
            (productTokens firsts seconds).reverse ++
              data.outputReverse }))
      (outerRowsTime seconds firsts) := by
  induction firsts generalizing data with
  | nil =>
      have run := EvalsToInTime.refl (TM2.step program)
        (scanOuterCfg data)
      have dataEq :
          { data with
            outer := outerTail
            source := seconds.flatMap DelimitedBinaryWords.wordTokens
            first := []
            firstOriginal := []
            sourceRestore := []
            outputReverse := data.outputReverse } = data := by
        cases data
        simp_all
      simpa [productTokens, outerRowsTime, dataEq] using run
  | cons first firsts induction =>
      let outerTail' :=
        firsts.flatMap DelimitedBinaryWords.wordTokens ++ outerTail
      let nextData : TapeData :=
        { data with
          outer := outerTail'
          source := seconds.flatMap DelimitedBinaryWords.wordTokens
          first := []
          firstOriginal := []
          sourceRestore := []
          outputReverse :=
            (rowTokens first seconds).reverse ++
              data.outputReverse }
      have firstRun := outerRow_evalsInTime first outerTail'
        seconds data
        (by simpa [outerTail', List.append_assoc] using outerEq)
        sourceEq firstEq firstOriginalEq sourceRestoreEq
      have rest := induction nextData rfl rfl rfl rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        (outerRowTime first seconds) (outerRowsTime seconds firsts)
        (scanOuterCfg data) (scanOuterCfg nextData)
        (some (scanOuterCfg
          { nextData with
            outer := outerTail
            source := seconds.flatMap DelimitedBinaryWords.wordTokens
            first := []
            firstOriginal := []
            sourceRestore := []
            outputReverse :=
              (productTokens firsts seconds).reverse ++
                nextData.outputReverse }))
        (by simpa [nextData, outerTail'] using firstRun) rest
      simpa only [productTokens, List.flatMap_cons, List.reverse_append,
        List.append_assoc, outerRowsTime, nextData, Nat.add_comm]
        using composed

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
