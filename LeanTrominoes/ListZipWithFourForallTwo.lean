/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Defs

/-! # Pointwise relations over four-list zips -/

namespace List

/-- Applying two four-column combiners to the same columns produces
pointwise-related outputs when the combiners are related at every first-column
entry. -/
theorem zipWith4_forall₂
    {First Second Third Fourth Left Right : Type*}
    (relation : Left → Right → Prop)
    (left : First → Second → Third → Fourth → Left)
    (right : First → Second → Third → Fourth → Right)
    (firsts : List First) (seconds : List Second)
    (thirds : List Third) (fourths : List Fourth)
    (related : ∀ first ∈ firsts, ∀ second third fourth,
      relation (left first second third fourth)
        (right first second third fourth)) :
    List.Forall₂ relation
      (List.zipWith4 left firsts seconds thirds fourths)
      (List.zipWith4 right firsts seconds thirds fourths) := by
  induction firsts generalizing seconds thirds fourths with
  | nil => exact List.Forall₂.nil
  | cons first firsts induction =>
      cases seconds with
      | nil => exact List.Forall₂.nil
      | cons second seconds =>
          cases thirds with
          | nil => exact List.Forall₂.nil
          | cons third thirds =>
              cases fourths with
              | nil => exact List.Forall₂.nil
              | cons fourth fourths =>
                  apply List.Forall₂.cons
                  · exact related first (by simp) second third fourth
                  · apply induction
                    intro item itemMember
                    exact related item (by simp [itemMember])

end List
