/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Support of item-indexed fixed candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

variable {Value Item : Type*} [DecidableEq Value]

/-- Activation-sensitive template correctness lifts pointwise through two
maps over the same item list. -/
theorem correctActiveTemplates_map
    (base : List Value) (items : List Item)
    (active : Item → Bool) (block : Item → List (Template Value))
    (correct : ∀ item ∈ items, if active item then
        ∀ template ∈ block item,
          template.supported = decide (template.value ∈ base)
      else True) :
    CorrectActiveTemplates base (items.map active) (items.map block) := by
  induction items with
  | nil => simp [CorrectActiveTemplates]
  | cons item items induction =>
      constructor
      · exact correct item (by simp)
      · exact induction (by
          intro tail tailMember
          exact correct tail (by simp [tailMember]))

end LeanTrominoes.PaddedSupportedCandidateBlocks
