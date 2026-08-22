/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastOccurrenceContributions
import LeanTrominoes.LastTrueUnaryValueLookupSemantics
import LeanTrominoes.PrefixSums
import Mathlib.Data.List.Dedup

/-! # Broadcasting last-occurrence-ordered block starts -/

namespace LeanTrominoes
namespace LastOccurrenceBlockStarts

variable {Value : Type*} [DecidableEq Value]

/-- The start of `target`'s block after an existing prefix, when distinct
blocks are ordered by their last occurrences in `remaining`. -/
def blockStartAux (all : List Value) (start : Nat)
    (remaining : List Value) (target : Value) : Nat :=
  start +
    (((remaining.dedup.take (remaining.dedup.idxOf target)).map
      fun value => all.count value).sum)

def blockStart (values : List Value) (target : Value) : Nat :=
  blockStartAux values 0 values target

def starts (values : List Value) : List Nat :=
  values.map (blockStart values)

/-- Looking up the prefix start at the last matching occurrence gives the
start of the corresponding last-occurrence-ordered block. -/
theorem lookup_eq_blockStartAux (all : List Value) (start : Nat)
    (remaining : List Value) (target : Value)
    (targetMem : target ∈ remaining) :
    LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow remaining target)
        (PrefixSums.startsAux start
          (LastOccurrenceContributions.contributionsAux all remaining)) =
      blockStartAux all start remaining target := by
  induction remaining generalizing start target with
  | nil => simp at targetMem
  | cons value remaining induction =>
      by_cases valueMem : value ∈ remaining
      · have targetTail : target ∈ remaining := by
          rcases (List.mem_cons.mp targetMem) with same | member
          · subst target
            exact valueMem
          · exact member
        by_cases same : target = value
        · subst target
          have candidateEq :=
            LastTrueUnaryValueLookupMachine.lookupAux_equalityRow_candidate_irrelevant
                start 0 value remaining
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all remaining)) valueMem
          calc
            LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow
                  (value :: remaining) value)
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all (value :: remaining))) =
              LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow remaining value)
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all remaining)) := by
                  simpa [LastTrueUnaryValueLookupMachine.lookup,
                    LastTrueUnaryValueLookupMachine.lookupAux,
                    StableOccurrenceRanks.equalityRow,
                    LastOccurrenceContributions.contributionsAux,
                    valueMem] using candidateEq
            _ = blockStartAux all start remaining value :=
              induction start value valueMem
            _ = blockStartAux all start (value :: remaining) value := by
              simp [blockStartAux, List.dedup_cons_of_mem valueMem]
        · calc
            LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow
                  (value :: remaining) target)
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all (value :: remaining))) =
              LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow remaining target)
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all remaining)) := by
                  simp [LastTrueUnaryValueLookupMachine.lookup,
                    LastTrueUnaryValueLookupMachine.lookupAux,
                    StableOccurrenceRanks.equalityRow,
                    LastOccurrenceContributions.contributionsAux,
                    valueMem, same]
            _ = blockStartAux all start remaining target :=
              induction start target targetTail
            _ = blockStartAux all start (value :: remaining) target := by
              simp [blockStartAux, List.dedup_cons_of_mem valueMem]
      · by_cases same : target = value
        · subst target
          have noLaterMatch :=
            LastTrueUnaryValueLookupMachine.lookupAux_equalityRow_of_not_mem
                start value remaining
                (PrefixSums.startsAux (start + all.count value)
                  (LastOccurrenceContributions.contributionsAux
                    all remaining)) valueMem
          calc
            LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow
                  (value :: remaining) value)
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all (value :: remaining))) =
              LastTrueUnaryValueLookupMachine.lookupAux start
                (StableOccurrenceRanks.equalityRow remaining value)
                (PrefixSums.startsAux (start + all.count value)
                  (LastOccurrenceContributions.contributionsAux
                    all remaining)) := by
                  simp [LastTrueUnaryValueLookupMachine.lookup,
                    LastTrueUnaryValueLookupMachine.lookupAux,
                    StableOccurrenceRanks.equalityRow,
                    LastOccurrenceContributions.contributionsAux,
                    valueMem]
            _ = start := noLaterMatch
            _ = blockStartAux all start (value :: remaining) value := by
              simp [blockStartAux,
                List.dedup_cons_of_notMem valueMem]
        · have targetTail : target ∈ remaining := by
            simpa [same] using targetMem
          calc
            LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow
                  (value :: remaining) target)
                (PrefixSums.startsAux start
                  (LastOccurrenceContributions.contributionsAux
                    all (value :: remaining))) =
              LastTrueUnaryValueLookupMachine.lookup
                (StableOccurrenceRanks.equalityRow remaining target)
                (PrefixSums.startsAux (start + all.count value)
                  (LastOccurrenceContributions.contributionsAux
                    all remaining)) := by
                  simp [LastTrueUnaryValueLookupMachine.lookup,
                    LastTrueUnaryValueLookupMachine.lookupAux,
                    StableOccurrenceRanks.equalityRow,
                    LastOccurrenceContributions.contributionsAux,
                    valueMem, same]
            _ = blockStartAux all (start + all.count value)
                remaining target :=
              induction (start + all.count value) target targetTail
            _ = blockStartAux all start (value :: remaining) target := by
              simp [blockStartAux,
                List.dedup_cons_of_notMem valueMem,
                List.idxOf_cons_ne _ (Ne.symm same),
                List.take_succ_cons, Nat.add_assoc]

/-- The complete lookup operation broadcasts each unique block start back to
every occurrence of its value. -/
theorem lookups_equalityRows_contributionStarts (values : List Value) :
    LastTrueUnaryValueLookupMachine.lookups
        (values.map (StableOccurrenceRanks.equalityRow values))
        (PrefixSums.starts
          (LastOccurrenceContributions.contributions values)) =
      starts values := by
  unfold LastTrueUnaryValueLookupMachine.lookups starts
  rw [List.map_map]
  apply List.map_congr_left
  intro target targetMem
  simpa [Function.comp_apply, blockStart, PrefixSums.starts,
    LastOccurrenceContributions.contributions] using
      lookup_eq_blockStartAux values 0 values target targetMem

end LastOccurrenceBlockStarts
end LeanTrominoes
