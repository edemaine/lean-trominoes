/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsActiveCandidateBlockSemantics

/-! # Item-indexed active datum blocks -/

namespace LeanTrominoes.FixedAxisUnaryFields

open PaddedSupportedCandidateBlocks

/-- Pointwise agreement lifts through three maps over the same item list. -/
theorem activeDatumBlocks_map
    {Item Value : Type*}
    (datum : Option Value → Nat) (items : List Item)
    (active : Item → Bool) (axes : Item → List Bool)
    (templates : Item → List (Template Value))
    (pointwise : ∀ item ∈ items,
      List.Forall₂
        (fun axis template =>
          value (active item) axis =
            datum (Template.activate (active item) template).value)
        (axes item) (templates item)) :
    ActiveDatumBlocks datum
      (items.map active) (items.map axes) (items.map templates) := by
  induction items with
  | nil => trivial
  | cons item items induction =>
      exact ⟨pointwise item (by simp),
        induction (fun tail tailMember =>
          pointwise tail (by simp [tailMember]))⟩

end LeanTrominoes.FixedAxisUnaryFields
