/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StableOccurrenceRanks
import LeanTrominoes.UnarySuccessorEqualityFilterInput

/-! # Stable occurrence ranks are below their multiplicities -/

namespace LeanTrominoes
namespace StableOccurrenceRanks

variable {Value : Type*} [DecidableEq Value]

def ranksAux_valid (seen remaining : List Value) :
    UnarySuccessorEqualityFilterMachine.Valid
      (ranksAux (seen ++ remaining) seen.length remaining)
      (remaining.map fun value => (seen ++ remaining).count value) := by
  induction remaining generalizing seen with
  | nil =>
      simp [ranksAux]
      exact .nil
  | cons value remaining induction =>
      apply UnarySuccessorEqualityFilterMachine.Valid.cons
      · simp [List.count_append]
      · have rest := induction (seen ++ [value])
        simpa [ranksAux, List.append_assoc] using rest

/-- Every stable rank counts a strict subset of all equal occurrences. -/
def ranks_valid (values : List Value) :
    UnarySuccessorEqualityFilterMachine.Valid
      (ranks values) (values.map fun value => values.count value) := by
  simpa [ranks] using ranksAux_valid ([] : List Value) values

end StableOccurrenceRanks
end LeanTrominoes
