/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPrefixRankAppend

/-! # Closed port-rank word for one occurrence cycle -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

def repeatPair (first second : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => first :: second :: repeatPair first second count

theorem flatMap_const_pair
    {Value : Type*} (values : List Value) (first second : Nat) :
    (values.flatMap fun _ => [first, second]) =
      repeatPair first second values.length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.flatMap_cons, List.length_cons, repeatPair]
      rw [induction]
      rfl

theorem rotate_repeatPair (count : Nat) :
    2 :: repeatPair 1 2 count ++ [2] =
      repeatPair 2 1 count ++ [2, 2] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [repeatPair]
      exact congrArg (fun ranks => 2 :: 1 :: ranks) induction

/-- The interleaved target-port ranks of one occurrence cycle. -/
def groupRankWord : Nat → List Nat
  | 0 => []
  | 1 => [1, 2]
  | count + 2 =>
      1 :: 1 :: repeatPair 2 1 count ++ [2, 2]

theorem prefixRanks_cycleLinkAtoms
    {Variable : Type*} [DecidableEq Variable]
    (values : List (ThreeOccurrenceVariable Variable))
    (nodup : values.Nodup) :
    prefixRanks (cycleLinkAtoms values) =
      groupRankWord values.length := by
  cases values with
  | nil => rfl
  | cons first rest =>
      rw [prefixRanks_cycleLinkAtoms_cons first rest nodup]
      cases rest with
      | nil => rfl
      | cons next rest =>
          rw [flatMap_const_pair]
          have rotated := rotate_repeatPair rest.length
          simpa only [List.length_cons, groupRankWord, repeatPair,
            List.cons_append]
            using congrArg (fun ranks => 1 :: 1 :: ranks) rotated

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
