/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Nodup

/-! # Enumerating indices with an explicit equality implementation -/

namespace LeanTrominoes
namespace List

/-- In a duplicate-free list, looking up every element with a fixed lawful
`BEq` enumerates exactly the consecutive list indices. -/
theorem map_idxOf_self_eq_range_beq
    {Value : Type*} [BEq Value] [LawfulBEq Value] [DecidableEq Value]
    (values : List Value) (nodup : values.Nodup) :
    values.map (fun value => values.idxOf value) =
      List.range values.length := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      have headNotMember : head ∉ tail :=
        (List.nodup_cons.mp nodup).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp nodup).2
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons]
      congr 1
      · simp
      rw [← induction tailNodup]
      rw [List.map_map]
      apply List.map_congr_left
      intro value valueMember
      have headNe : head ≠ value := by
        intro equal
        exact headNotMember (equal ▸ valueMember)
      simp [headNe]

end List
end LeanTrominoes
