/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualityPairExecution

/-! # Pair-list execution for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

def pairsTime : List (List Bool × List Bool) → Nat
  | [] => 1
  | pair :: pairs => pairTime pair.1 pair.2 + pairsTime pairs

def pairResults (pairs : List (List Bool × List Bool)) : List Bool :=
  pairs.map fun pair => decide (pair.1 = pair.2)

def pairs_evalsInTime (pairs : List (List Bool × List Bool))
    (resultReverse output : List Bool) :
    EvalsToInTime (TM2.step program)
      (scanCfg
        ⟨pairs.flatMap pairTokens, [], [], resultReverse, output⟩)
      (some (reverseCfg
        ⟨[], [], [], (pairResults pairs).reverse ++ resultReverse, output⟩))
      (pairsTime pairs) := by
  induction pairs generalizing resultReverse with
  | nil =>
      have step := oneStep (step_scan_nil
        ⟨[], [], [], resultReverse, output⟩ rfl)
      convert step using 1 <;> simp [pairsTime, pairResults]
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      have pairRun := pair_evalsInTime first second
        (pairs.flatMap pairTokens) resultReverse output
      have rest := induction
        (decide (first = second) :: resultReverse)
      have composed := EvalsToInTime.trans (TM2.step program)
        (pairTime first second) (pairsTime pairs)
        (scanCfg
          ⟨pairTokens (first, second) ++ pairs.flatMap pairTokens,
            [], [], resultReverse, output⟩)
        (scanCfg
          ⟨pairs.flatMap pairTokens, [], [],
            decide (first = second) :: resultReverse, output⟩)
        (some (reverseCfg
          ⟨[], [], [],
            (pairResults pairs).reverse ++
              decide (first = second) :: resultReverse,
            output⟩))
        pairRun rest
      simpa only [List.flatMap_cons, pairsTime, pairResults, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append,
        Prod.fst, Prod.snd,
        Nat.add_comm] using composed

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
