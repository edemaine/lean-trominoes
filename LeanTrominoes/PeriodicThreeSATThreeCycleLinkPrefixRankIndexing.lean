/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkGroupedPortRanks

/-! # Stable-index semantics of prefix ranks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

def indexedPrefixRanksFrom {Value : Type*} [BEq Value]
    (seen values : List Value) : List Nat :=
  values.zipIdx.map fun tagged =>
    1 + (seen ++ values.take tagged.2).count tagged.1

def indexedPrefixRanks {Value : Type*} [BEq Value]
    (values : List Value) : List Nat :=
  values.zipIdx.map fun tagged =>
    1 + (values.take tagged.2).count tagged.1

theorem prefixRanksFrom_eq_indexedPrefixRanksFrom
    {Value : Type*} [BEq Value]
    (seen values : List Value) :
    prefixRanksFrom seen values = indexedPrefixRanksFrom seen values := by
  induction values generalizing seen with
  | nil => rfl
  | cons value values induction =>
      rw [prefixRanksFrom]
      unfold indexedPrefixRanksFrom
      rw [List.zipIdx_cons, List.map_cons]
      congr 1
      · simp
      · rw [induction]
        unfold indexedPrefixRanksFrom
        simp only [Nat.zero_add]
        conv_rhs => rw [List.zipIdx_eq_map_add]
        rw [List.map_map]
        apply List.map_congr_left
        intro tagged _
        dsimp
        rw [show 1 + tagged.2 = tagged.2 + 1 by omega]
        rw [List.take_succ_cons]
        congr 2
        simp [List.append_assoc]

theorem prefixRanks_eq_indexedPrefixRanks
    {Value : Type*} [BEq Value] (values : List Value) :
    prefixRanks values = indexedPrefixRanks values := by
  simpa [prefixRanks, indexedPrefixRanks, indexedPrefixRanksFrom] using
    prefixRanksFrom_eq_indexedPrefixRanksFrom ([] : List Value) values

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
