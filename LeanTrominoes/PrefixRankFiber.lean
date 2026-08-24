/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPrefixRankData

/-! # Fibers of prefix multiplicity ranks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

/-- Selecting one key from a prefix-rank word yields a consecutive interval
starting after the copies of that key already seen. -/
theorem prefixRanksFrom_fiber_eq_range'
    {Value : Type*} [DecidableEq Value]
    (seen values : List Value) (key : Value) :
    ((values.zip (prefixRanksFrom seen values)).flatMap fun pair =>
        if pair.1 = key then [pair.2] else []) =
      List.range' (1 + seen.count key) (values.count key) := by
  induction values generalizing seen with
  | nil => simp [prefixRanksFrom]
  | cons value values induction =>
      by_cases valueEq : value = key
      · subst value
        simp [prefixRanksFrom, induction, List.range'_succ,
          List.count_append, Nat.add_assoc]
      · simp [prefixRanksFrom, valueEq, induction,
          List.count_append]

/-- In a word where `key` occurs twice, its one-based prefix ranks are
exactly one and two. -/
theorem prefixRanks_fiber_eq_one_two
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (key : Value)
    (twice : values.count key = 2) :
    ((values.zip (prefixRanks values)).flatMap fun pair =>
        if pair.1 = key then [pair.2] else []) = [1, 2] := by
  rw [show prefixRanks values = prefixRanksFrom [] values by rfl,
    prefixRanksFrom_fiber_eq_range', twice]
  rfl

/-- The same two-rank fiber theorem before mapping a structured presentation
to its keys. -/
theorem mappedPrefixRanks_fiber_eq_one_two
    {Value Key : Type*} [DecidableEq Key]
    (values : List Value) (keyOf : Value → Key) (key : Key)
    (twice : (values.map keyOf).count key = 2) :
    ((values.zip (prefixRanks (values.map keyOf))).flatMap fun pair =>
        if keyOf pair.1 = key then [pair.2] else []) = [1, 2] := by
  simpa [List.zip_map_left, List.flatMap_map] using
    prefixRanks_fiber_eq_one_two (values.map keyOf) key twice

/-- Selecting one key from the indexed prefix-count presentation yields the
same consecutive rank interval. -/
theorem indexedPrefixCount_fiber_eq_range'
    {Value Key : Type*} [DecidableEq Key]
    (seen : List Key) (values : List Value)
    (keyOf : Value → Key) (key : Key) :
    (values.zipIdx.flatMap fun tagged =>
        if keyOf tagged.1 = key then
          [1 + (seen ++ (values.map keyOf).take tagged.2).count key]
        else []) =
      List.range' (1 + seen.count key)
        ((values.map keyOf).count key) := by
  induction values generalizing seen with
  | nil => simp
  | cons value values induction =>
      rw [List.zipIdx_cons, List.flatMap_cons,
        List.zipIdx_eq_map_add, List.flatMap_map]
      simp only [Nat.add_comm]
      by_cases valueEq : keyOf value = key
      · simp [valueEq, List.count_append,
          List.range'_succ, Nat.add_assoc]
        convert induction (seen ++ [keyOf value]) using 1
        all_goals simp [List.count_append, valueEq] <;> try omega
      · simp [valueEq, List.count_append]
        convert induction (seen ++ [keyOf value]) using 1
        all_goals simp [List.count_append, valueEq] <;> try omega

/-- A key occurring twice has indexed prefix counts one and two. -/
theorem indexedPrefixCount_fiber_eq_one_two
    {Value Key : Type*} [DecidableEq Key]
    (values : List Value) (keyOf : Value → Key) (key : Key)
    (twice : (values.map keyOf).count key = 2) :
    (values.zipIdx.flatMap fun tagged =>
        if keyOf tagged.1 = key then
          [1 + ((values.map keyOf).take tagged.2).count key]
        else []) = [1, 2] := by
  calc
    _ = List.range' 1 2 := by
      simpa only [List.nil_append, List.count_nil, Nat.add_zero, twice]
        using indexedPrefixCount_fiber_eq_range'
          ([] : List Key) values keyOf key
    _ = [1, 2] := by rfl

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
