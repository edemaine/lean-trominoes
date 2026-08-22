/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksMachine
import Mathlib.Data.List.Basic

/-! # Element indices after rotating a list's head to its tail -/

namespace LeanTrominoes
namespace RotatedListIndex

variable {Value : Type*} [DecidableEq Value]

/-- In a duplicate-free list, `tail ++ take 1` moves local index zero to the
last position and decrements every positive local index. -/
theorem idxOf_tail_append_take_one (values : List Value)
    (nodup : values.Nodup) (value : Value) (valueMem : value ∈ values) :
    (values.tail ++ values.take 1).idxOf value =
      UnaryRotatedRanksMachine.rotatedRank
        (values.idxOf value) values.length := by
  cases values with
  | nil => simp at valueMem
  | cons head tail =>
      have headNotTail : head ∉ tail := (List.nodup_cons.mp nodup).1
      by_cases same : value = head
      · subst value
        change (tail ++ [head]).idxOf head =
          UnaryRotatedRanksMachine.rotatedRank
            ((head :: tail).idxOf head) (tail.length + 1)
        rw [List.idxOf_append_of_notMem headNotTail]
        simp [UnaryRotatedRanksMachine.rotatedRank]
      · have valueMemTail : value ∈ tail := by
          simpa [same] using valueMem
        change (tail ++ [head]).idxOf value =
          UnaryRotatedRanksMachine.rotatedRank
            ((head :: tail).idxOf value) (tail.length + 1)
        rw [List.idxOf_append_of_mem valueMemTail]
        simp [List.idxOf_cons_ne _ (Ne.symm same),
          UnaryRotatedRanksMachine.rotatedRank]

end RotatedListIndex
end LeanTrominoes
