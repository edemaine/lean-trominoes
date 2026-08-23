/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkGroupedPortRanks
import Mathlib.Data.List.Dedup

/-! # Selecting doubled keys at their second occurrence -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

/-- If every remaining key occurs twice in the complete presentation, then
selecting rank two from the prefix-rank stream retains exactly the final
representative of each key. -/
theorem prefixRanksFrom_rankTwo_flatMap_eq_dedup
    {Value Output : Type*} [DecidableEq Value]
    (seen remaining : List Value)
    (twice : ∀ value ∈ remaining,
      (seen ++ remaining).count value = 2)
    (block : Value → List Output) :
    ((remaining.zip (prefixRanksFrom seen remaining)).flatMap fun pair =>
        if pair.2 = 2 then block pair.1 else []) =
      remaining.dedup.flatMap block := by
  induction remaining generalizing seen with
  | nil => rfl
  | cons value remaining induction =>
      have total := twice value List.mem_cons_self
      have totalEq :
          seen.count value + (remaining.count value + 1) = 2 := by
        simpa [List.count_append] using total
      have rankTwoIff : 1 + seen.count value = 2 ↔
          value ∉ remaining := by
        constructor
        · intro rankTwo valueMember
          have positive : 0 < remaining.count value :=
            List.count_pos_iff.mpr valueMember
          omega
        · intro valueNotMember
          have zero : remaining.count value = 0 :=
            List.count_eq_zero.mpr valueNotMember
          omega
      have tailTwice : ∀ later ∈ remaining,
          ((seen ++ [value]) ++ remaining).count later = 2 := by
        intro later laterMember
        simpa [List.append_assoc] using
          twice later (List.mem_cons_of_mem value laterMember)
      have tail := induction (seen ++ [value]) tailTwice
      simp only [prefixRanksFrom, List.zip_cons_cons, List.flatMap_cons]
      rw [tail]
      by_cases valueMember : value ∈ remaining
      · rw [List.dedup_cons_of_mem valueMember]
        simp [rankTwoIff, valueMember]
      · rw [List.dedup_cons_of_notMem valueMember, List.flatMap_cons]
        simp [rankTwoIff, valueMember]

/-- For a word in which every key occurs exactly twice, its rank-two blocks
are its deduplicated blocks in Lean's last-occurrence order. -/
theorem prefixRanks_rankTwo_flatMap_eq_dedup
    {Value Output : Type*} [DecidableEq Value]
    (values : List Value)
    (twice : ∀ value ∈ values, values.count value = 2)
    (block : Value → List Output) :
    ((values.zip (prefixRanks values)).flatMap fun pair =>
        if pair.2 = 2 then block pair.1 else []) =
      values.dedup.flatMap block := by
  simpa [prefixRanks] using
    prefixRanksFrom_rankTwo_flatMap_eq_dedup
      ([] : List Value) values (by simpa using twice) block

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
