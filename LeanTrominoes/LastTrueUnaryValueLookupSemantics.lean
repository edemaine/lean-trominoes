/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.StableOccurrenceRanks

/-! # Semantics of last-true lookup on equality rows -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

variable {Value : Type*} [DecidableEq Value]

/-- If an equality row has no true bit, scanning it preserves the incoming
candidate, independently of the aligned value stream. -/
theorem lookupAux_equalityRow_of_not_mem (candidate : Nat)
    (target : Value) (remaining : List Value) (starts : List Nat)
    (notMem : target ∉ remaining) :
    lookupAux candidate
        (StableOccurrenceRanks.equalityRow remaining target) starts =
      candidate := by
  induction remaining generalizing starts with
  | nil => simp [StableOccurrenceRanks.equalityRow, lookupAux]
  | cons value remaining induction =>
      have headNe : target ≠ value := by
        intro equal
        subst value
        exact notMem (by simp)
      have tailNotMem : target ∉ remaining := by
        intro member
        exact notMem (by simp [member])
      cases starts with
      | nil =>
          simpa [StableOccurrenceRanks.equalityRow, lookupAux, headNe] using
            induction ([] : List Nat) tailNotMem
      | cons start starts =>
          simpa [StableOccurrenceRanks.equalityRow, lookupAux, headNe] using
            induction starts tailNotMem

/-- Once an equality-row tail contains a true bit, its final selected value
does not depend on the candidate inherited from the prefix. -/
theorem lookupAux_equalityRow_candidate_irrelevant
    (first second : Nat) (target : Value) (remaining : List Value)
    (starts : List Nat) (member : target ∈ remaining) :
    lookupAux first
        (StableOccurrenceRanks.equalityRow remaining target) starts =
      lookupAux second
        (StableOccurrenceRanks.equalityRow remaining target) starts := by
  induction remaining generalizing starts first second with
  | nil => simp at member
  | cons value remaining induction =>
      by_cases same : target = value
      · subst value
        cases starts <;>
          simp [StableOccurrenceRanks.equalityRow, lookupAux]
      · have tailMember : target ∈ remaining := by
          simpa [same] using member
        cases starts with
        | nil =>
            simpa [StableOccurrenceRanks.equalityRow, lookupAux, same] using
              induction first second ([] : List Nat) tailMember
        | cons start starts =>
            simpa [StableOccurrenceRanks.equalityRow, lookupAux, same] using
              induction first second starts tailMember

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
