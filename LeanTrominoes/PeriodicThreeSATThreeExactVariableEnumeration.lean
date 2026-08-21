/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleExactOccurrences
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount
import Mathlib.Data.Multiset.Dedup

/-! # Exact variable enumeration after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Within a directed occurrence cycle, last-occurrence deduplication retains
the current copy, the remaining copies, and finally the closing first copy. -/
theorem cycleFrom_variableOccurrences_dedup_of_nodup
    {Variable : Type*} [DecidableEq (ThreeOccurrenceVariable Variable)]
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (nodup : (first :: current :: rest).Nodup) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cycleFrom first current rest))).dedup =
        current :: rest ++ [first] := by
  induction rest generalizing current with
  | nil =>
      apply List.dedup_eq_self.mpr
      simpa [cycleFrom, implicationClause,
        PeriodicCNF.variableOccurrences, ne_comm] using nodup
  | cons next rest induction =>
      have firstNotTail : first ∉ current :: next :: rest :=
        (List.nodup_cons.mp nodup).1
      have tailNodup : (current :: next :: rest).Nodup :=
        (List.nodup_cons.mp nodup).2
      have currentNotTail : current ∉ next :: rest :=
        (List.nodup_cons.mp tailNodup).1
      have recursiveNodup : (first :: next :: rest).Nodup := by
        apply List.Nodup.cons
        · intro firstMember
          exact firstNotTail (List.mem_cons_of_mem current firstMember)
        · exact tailNodup.of_cons
      let recursiveOccurrences :=
        PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (cycleFrom first next rest))
      have recursiveOrder : recursiveOccurrences.dedup =
          next :: rest ++ [first] :=
        induction next recursiveNodup
      have nextMem : next ∈ recursiveOccurrences := by
        rw [← List.mem_dedup, recursiveOrder]
        simp
      have currentNotRecursive : current ∉ recursiveOccurrences := by
        intro currentMember
        have contained := cycleFrom_variableOccurrences_subset
          first next rest currentMember
        have currentNotAll : current ∉ first :: next :: rest := by
          intro currentAll
          simp only [List.mem_cons] at currentAll
          rcases currentAll with currentEq | currentTail
          · exact firstNotTail (currentEq.symm ▸ List.mem_cons_self)
          · exact currentNotTail (by
              simpa only [List.mem_cons] using currentTail)
        exact currentNotAll contained
      have currentNeNext : current ≠ next := by
        intro currentEq
        exact currentNotTail (currentEq ▸ List.mem_cons_self)
      rw [show PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (cycleFrom first current (next :: rest))) =
            current :: next :: recursiveOccurrences by
        simp [cycleFrom, implicationClause,
          PeriodicCNF.variableOccurrences, recursiveOccurrences]]
      rw [List.dedup_cons_of_notMem (by
          simp [currentNeNext, currentNotRecursive]),
        List.dedup_cons_of_mem nextMem, recursiveOrder]
      simp only [List.cons_append]

/-- A nonempty cycle's exact variable order after deduplication is its tail
followed by its first copy. -/
theorem cycleClauses_variableOccurrences_dedup_of_nodup
    {Variable : Type*} [DecidableEq (ThreeOccurrenceVariable Variable)]
    (copies : List (ThreeOccurrenceVariable Variable))
    (nodup : copies.Nodup) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cycleClauses copies))).dedup =
        copies.tail ++ copies.take 1 := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil =>
          simp [cycleClauses, cycleFrom, implicationClause,
            PeriodicCNF.variableOccurrences]
      | cons next rest =>
          unfold cycleClauses
          have recursiveNodup : (first :: next :: rest).Nodup := nodup
          have exactOrder :=
            cycleFrom_variableOccurrences_dedup_of_nodup
              first next rest recursiveNodup
          let recursiveOccurrences :=
            PeriodicCNF.variableOccurrences
              (PeriodicCNF.mk (cycleFrom first next rest))
          have firstMem : first ∈ recursiveOccurrences := by
            rw [← List.mem_dedup, exactOrder]
            simp
          have nextMem : next ∈ recursiveOccurrences := by
            rw [← List.mem_dedup, exactOrder]
            simp
          rw [show PeriodicCNF.variableOccurrences
              (PeriodicCNF.mk (cycleFrom first first (next :: rest))) =
                [first, next] ++ recursiveOccurrences by
            simp [cycleFrom, implicationClause,
              PeriodicCNF.variableOccurrences, recursiveOccurrences]]
          rw [List.Subset.dedup_append_right (by
            intro copy copyMember
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at copyMember
            rcases copyMember with rfl | rfl
            · exact firstMem
            · exact nextMem), exactOrder]
          rfl

end PeriodicThreeSATThree
end LeanTrominoes
