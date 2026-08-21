/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductOnePairExecution

/-! # One row of the binary-word ordered product -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def rowTokens (first : List Bool) (seconds : List (List Bool)) :
    List PairToken :=
  seconds.flatMap fun second =>
    DelimitedBinaryWordPairs.pairTokens (first, second)

def rowTime (first : List Bool) : List (List Bool) → Nat
  | [] => 1
  | second :: seconds => pairTime first second + rowTime first seconds

def row_evalsInTime (first : List Bool)
    (seconds : List (List Bool)) (data : TapeData)
    (sourceEq : data.source =
      seconds.flatMap DelimitedBinaryWords.wordTokens)
    (firstEq : data.first = [])
    (firstOriginalEq : data.firstOriginal = first) :
    EvalsToInTime (TM2.step program) (scanInnerCfg data)
      (some (restoreSourceCfg
        { data with
          source := []
          first := []
          firstOriginal := first
          sourceRestore :=
            (seconds.flatMap
              DelimitedBinaryWords.wordTokens).reverse ++
                data.sourceRestore
          outputReverse :=
            (rowTokens first seconds).reverse ++ data.outputReverse }))
      (rowTime first seconds) := by
  induction seconds generalizing data with
  | nil =>
      have step := oneStep (step_scanInner_nil data (by
        simpa using sourceEq))
      convert step using 1 <;> simp [rowTokens, rowTime,
        firstEq, firstOriginalEq]
  | cons second seconds induction =>
      have pairRun := pair_evalsInTime first second
        (seconds.flatMap DelimitedBinaryWords.wordTokens) data
        (by simpa using sourceEq) firstEq firstOriginalEq
      let nextData : TapeData :=
        { data with
          source := seconds.flatMap DelimitedBinaryWords.wordTokens
          first := []
          firstOriginal := first
          sourceRestore :=
            (DelimitedBinaryWords.wordTokens second).reverse ++
              data.sourceRestore
          outputReverse :=
            (DelimitedBinaryWordPairs.pairTokens
              (first, second)).reverse ++ data.outputReverse }
      have rest := induction nextData rfl rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        (pairTime first second) (rowTime first seconds)
        (scanInnerCfg data) (scanInnerCfg nextData)
        (some (restoreSourceCfg
          { nextData with
            source := []
            first := []
            firstOriginal := first
            sourceRestore :=
              (seconds.flatMap
                DelimitedBinaryWords.wordTokens).reverse ++
                  nextData.sourceRestore
            outputReverse :=
              (rowTokens first seconds).reverse ++
                nextData.outputReverse }))
        (by simpa [nextData] using pairRun) rest
      simpa only [List.flatMap_cons, rowTokens, rowTime,
        List.reverse_append, List.append_assoc, Nat.add_comm]
        using composed

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
