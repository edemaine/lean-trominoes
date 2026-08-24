/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomCycleSemantics

/-! # Endpoint multiplicity within one occurrence cycle -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

private theorem count_flatMap_double
    {Value : Type*} [BEq Value] [LawfulBEq Value]
    (values : List Value) (target : Value) :
    (values.flatMap fun value => [value, value]).count target =
      2 * values.count target := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases same : value = target
      · subst value
        simp [induction]
        omega
      · simp [same, induction]

/-- In a duplicate-free cycle, every presented endpoint occurs exactly
twice in its alternating source/target endpoint word. -/
theorem cycleLinkAtoms_count_eq_two_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (values : List (ThreeOccurrenceVariable Variable))
    (valuesNodup : values.Nodup)
    (value : ThreeOccurrenceVariable Variable)
    (valueMember : value ∈ cycleLinkAtoms values) :
    (cycleLinkAtoms values).count value = 2 := by
  cases values with
  | nil => simp [cycleLinkAtoms, cycleLinks, linkAtoms] at valueMember
  | cons first rest =>
      have firstNotRest := (List.nodup_cons.mp valuesNodup).1
      have restNodup := (List.nodup_cons.mp valuesNodup).2
      rw [cycleLinkAtoms_cons] at valueMember ⊢
      rw [List.count_append]
      by_cases same : value = first
      · subst value
        have restCountZero : rest.count first = 0 :=
          List.count_eq_zero.mpr firstNotRest
        rw [List.count_cons_self, List.count_singleton_self,
          count_flatMap_double rest first, restCountZero]
      · have valueMemberRest : value ∈ rest := by
          simpa [same] using valueMember
        have restCountOne : rest.count value = 1 :=
          List.count_eq_one_of_mem restNodup valueMemberRest
        have firstNeValue : first ≠ value := Ne.symm same
        have singletonZero : ([first] :
            List (ThreeOccurrenceVariable Variable)).count value = 0 :=
          List.count_eq_zero.mpr (by simp [same])
        rw [List.count_cons_of_ne firstNeValue, singletonZero,
          Nat.add_zero, count_flatMap_double rest value, restCountOne]

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
