/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPrefixRankIndexing

/-! # Prefix ranks across disjoint words -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

theorem prefixRanksFrom_append
    {Value : Type*} [BEq Value]
    (seen first second : List Value) :
    prefixRanksFrom seen (first ++ second) =
      prefixRanksFrom seen first ++
        prefixRanksFrom (seen ++ first) second := by
  induction first generalizing seen with
  | nil => simp only [List.nil_append, List.append_nil, prefixRanksFrom]
  | cons value first induction =>
      have seenEq : (seen ++ [value]) ++ first =
          seen ++ (value :: first) := by
        simp only [List.append_assoc, List.singleton_append]
      change (1 + seen.count value) ::
          prefixRanksFrom (seen ++ [value]) (first ++ second) =
        (1 + seen.count value) ::
          (prefixRanksFrom (seen ++ [value]) first ++
            prefixRanksFrom (seen ++ (value :: first)) second)
      rw [induction, seenEq]

theorem prefixRanksFrom_congr_seen
    {Value : Type*} [BEq Value]
    (firstSeen secondSeen values : List Value)
    (counts : ∀ value ∈ values,
      firstSeen.count value = secondSeen.count value) :
    prefixRanksFrom firstSeen values =
      prefixRanksFrom secondSeen values := by
  induction values generalizing firstSeen secondSeen with
  | nil => rfl
  | cons value values induction =>
      rw [prefixRanksFrom, prefixRanksFrom,
        counts value List.mem_cons_self]
      congr 1
      apply induction
      intro later laterMember
      rw [List.count_append, List.count_append,
        counts later (List.mem_cons_of_mem value laterMember)]

theorem prefixRanksFrom_eq_prefixRanks_of_disjoint
    {Value : Type*} [BEq Value] [LawfulBEq Value]
    (seen values : List Value) (disjoint : List.Disjoint seen values) :
    prefixRanksFrom seen values = prefixRanks values := by
  unfold prefixRanks
  apply prefixRanksFrom_congr_seen
  intro value valueMember
  have notSeen : value ∉ seen := by
    intro seenMember
    exact (List.disjoint_left.mp disjoint) seenMember valueMember
  rw [List.count_eq_zero_of_not_mem notSeen]
  simp

theorem prefixRanks_append_of_disjoint
    {Value : Type*} [BEq Value] [LawfulBEq Value]
    (first second : List Value) (disjoint : List.Disjoint first second) :
    prefixRanks (first ++ second) =
      prefixRanks first ++ prefixRanks second := by
  calc
    prefixRanks (first ++ second) =
        prefixRanksFrom [] first ++ prefixRanksFrom first second := by
      simpa [prefixRanks] using prefixRanksFrom_append
        ([] : List Value) first second
    _ = prefixRanks first ++ prefixRanks second := by
      rw [prefixRanksFrom_eq_prefixRanks_of_disjoint
        first second disjoint]
      rfl

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
