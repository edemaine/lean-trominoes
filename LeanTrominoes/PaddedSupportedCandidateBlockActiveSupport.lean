/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockSupport

/-! # Support from membership of active fixed-block values -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value Item : Type*} [DecidableEq Value]

/-- If every template is tagged supported and every active value lies in the
base, then the activation-sensitive template invariant holds. -/
theorem correctActiveTemplates_of_supported_true
    (base : List Value) (actives : List Bool)
    (blocks : List (List (Template Value)))
    (supportedTrue : ∀ template ∈ blocks.flatten,
      template.supported = true)
    (activeSubset : activeValues actives blocks ⊆ base) :
    CorrectActiveTemplates base actives blocks := by
  induction actives generalizing blocks with
  | nil => simp [CorrectActiveTemplates]
  | cons active actives induction =>
      cases blocks with
      | nil => simp [CorrectActiveTemplates]
      | cons block blocks =>
          have tailSupported : ∀ template ∈ blocks.flatten,
              template.supported = true := by
            intro template member
            exact supportedTrue template (by simp [member])
          have tailSubset : activeValues actives blocks ⊆ base := by
            intro value member
            apply activeSubset
            cases active <;> simp [activeValues, member]
          constructor
          · cases active with
            | false => simp
            | true =>
                simp only [if_true]
                intro template templateMember
                rw [supportedTrue template (by simp [templateMember])]
                have valueMember :
                    template.value ∈
                      activeValues (true :: actives) (block :: blocks) := by
                  rw [activeValues]
                  simp only [if_true]
                  exact List.mem_append_left _
                    (List.mem_map.mpr
                      ⟨template, templateMember, rfl⟩)
                simp [activeSubset valueMember]
          · exact induction blocks tailSupported tailSubset

/-- Correct support is preserved by flattening an item-indexed family whose
every candidate block is correctly tagged. -/
theorem correctSupport_flatMap
    (base : List Value) (items : List Item)
    (block : Item → List (Candidate Value))
    (correct : ∀ item ∈ items, CorrectSupport base (block item)) :
    CorrectSupport base (items.flatMap block) := by
  induction items with
  | nil => intro candidate member; simp at member
  | cons item items induction =>
      rw [List.flatMap_cons]
      exact correctSupport_append base _ _
        (correct item (by simp))
        (induction (by
          intro tail tailMember
          exact correct tail (by simp [tailMember])))

end LeanTrominoes.PaddedSupportedCandidateBlocks
