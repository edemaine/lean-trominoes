/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPositionPortRankWord

/-! # Equality of occurrence-count implementations -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Structural product equality and equality synthesized from `DecidableEq`
count occurrence-copy values identically. -/
theorem occurrenceVariable_count_eq_decidable
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (value : ThreeOccurrenceVariable Variable)
    (values : List (ThreeOccurrenceVariable Variable)) :
    @List.count (ThreeOccurrenceVariable Variable) instBEqProd value values =
      @List.count (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq value values := by
  induction values with
  | nil => rfl
  | cons head values induction =>
      by_cases equal : head = value
      · subst head
        simp [induction]
      · simp [equal, induction]

end PeriodicThreeSATThree
end LeanTrominoes
