/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Element indices in flattened keyed blocks -/

namespace LeanTrominoes
namespace GroupedListIndex

/-- In a flattened family whose blocks contain only values with their
advertised key, a target's global index is its preceding block length plus
its local index. -/
theorem idxOf_flatMap_eq_prefix_sum_add_local
    {Key Value : Type*} [DecidableEq Key] [DecidableEq Value]
    (keys : List Key) (block : Key → List Value) (keyOf : Value → Key)
    (targetKey : Key) (target : Value)
    (blocksHaveKey : ∀ key value, value ∈ block key → keyOf value = key)
    (targetKeyEq : keyOf target = targetKey)
    (targetKeyMem : targetKey ∈ keys)
    (targetMem : target ∈ block targetKey) :
    @List.idxOf Value instBEqOfDecidableEq target (keys.flatMap block) =
      (((keys.take (@List.idxOf Key instBEqOfDecidableEq
        targetKey keys)).map fun key => (block key).length).sum) +
        @List.idxOf Value instBEqOfDecidableEq target (block targetKey) := by
  letI : BEq Key := instBEqOfDecidableEq
  letI : BEq Value := instBEqOfDecidableEq
  induction keys with
  | nil => simp at targetKeyMem
  | cons head keys induction =>
      by_cases same : head = targetKey
      · subst head
        rw [List.flatMap_cons,
          List.idxOf_append_of_mem targetMem]
        simp
      · have targetKeyMemTail : targetKey ∈ keys := by
          simpa [same, Ne.symm same] using targetKeyMem
        have targetNotHeadBlock : target ∉ block head := by
          intro targetMember
          have keyEq := blocksHaveKey head target targetMember
          exact same (keyEq ▸ targetKeyEq)
        rw [List.flatMap_cons,
          List.idxOf_append_of_notMem targetNotHeadBlock,
          induction targetKeyMemTail]
        simp [same, List.take_succ_cons]
        omega

end GroupedListIndex
end LeanTrominoes
