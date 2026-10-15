/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Filtering an injectively keyed mapped list -/

namespace LeanTrominoes

/-- Filtering an injectively keyed, duplicate-free mapped list at the key of
one selected source returns its unique image exactly when the source occurs. -/
theorem filter_map_key_eq
    {Source Target Key : Type*}
    [DecidableEq Source] [DecidableEq Key]
    (values : List Source) (nodup : values.Nodup)
    (mapValue : Source → Target) (key : Target → Key)
    (keyInjective : Function.Injective (key ∘ mapValue))
    (selected : Source) :
    (values.map mapValue).filter
        (fun value => key value = key (mapValue selected)) =
      if selected ∈ values then [mapValue selected] else [] := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have valueNotValues := (List.nodup_cons.mp nodup).1
      have valuesNodup := (List.nodup_cons.mp nodup).2
      have keyEq :
          key (mapValue value) = key (mapValue selected) ↔
            value = selected := by
        constructor
        · intro keyEquality
          apply keyInjective
          exact keyEquality
        · intro equal
          exact congrArg (key ∘ mapValue) equal
      by_cases equal : value = selected
      · subst value
        simp [valueNotValues, induction valuesNodup]
      · have equalSymm : ¬selected = value := by
          intro selectedEq
          exact equal selectedEq.symm
        simp [keyEq, equal, equalSymm, induction valuesNodup]

end LeanTrominoes
