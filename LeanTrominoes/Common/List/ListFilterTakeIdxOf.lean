/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Filtered presentation prefixes before a target -/

namespace List

/-- Taking a filtered list before a selected member gives exactly the
selected values before that member in the original presentation. -/
theorem take_idxOf_filter_eq_filter_take_idxOf
    {Value : Type*} [DecidableEq Value] [BEq Value] [LawfulBEq Value]
    (selected : Value → Bool) (values : List Value) (target : Value)
    (targetMember : target ∈ values)
    (targetSelected : selected target = true) :
    (values.filter selected).take ((values.filter selected).idxOf target) =
      (values.take (values.idxOf target)).filter selected := by
  induction values with
  | nil => simp at targetMember
  | cons head tail induction =>
      by_cases same : head = target
      · subst head
        simp [targetSelected]
      · have targetMemberTail : target ∈ tail := by
          simpa [same, Ne.symm same] using targetMember
        have tailEquality := induction targetMemberTail
        cases headSelected : selected head <;>
          simp [same, headSelected, tailEquality]

end List
