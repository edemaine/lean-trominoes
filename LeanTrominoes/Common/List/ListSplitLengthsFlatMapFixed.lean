/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.SplitLengths

/-! # Splitting a flat map into fixed-width blocks -/

namespace LeanTrominoes
namespace List

/-- Splitting a flat map at the common block width recovers the original
blocks. -/
theorem replicate_splitLengths_flatMap_of_length_eq
    {Value Output : Type*}
    (values : List Value) (block : Value → List Output) (width : Nat)
    (blockLength : ∀ value, (block value).length = width) :
    (List.replicate values.length width).splitLengths
        (values.flatMap block) =
      values.map block := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have takeBlock :
          (block value ++ values.flatMap block).take width =
            block value := by
        rw [← blockLength value]
        simp
      have dropBlock :
          (block value ++ values.flatMap block).drop width =
            values.flatMap block := by
        rw [← blockLength value]
        simp
      rw [List.length_cons, List.replicate_succ, List.flatMap_cons,
        List.splitLengths_cons, List.map_cons, takeBlock, dropBlock,
        induction]

end List
end LeanTrominoes
