/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Activity support of fixed candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value Item : Type*}

/-- Activating a template whose support bit is true makes support exactly
option activity. -/
theorem Template.activate_supported_eq_isSome
    (template : Template Value) (active : Bool)
    (supported : template.supported = true) :
    (template.activate active).supported =
      (template.activate active).value.isSome := by
  cases active <;> simp [Template.activate, supported]

/-- Aligned activation of all-true template blocks produces candidates whose
support bits are exactly their option activity. -/
theorem candidates_supported_eq_isSome
    (actives : List Bool) (blocks : List (List (Template Value)))
    (supportedTrue : ∀ template ∈ blocks.flatten,
      template.supported = true) :
    ∀ candidate ∈ candidates actives blocks,
      candidate.supported = candidate.value.isSome := by
  induction actives generalizing blocks with
  | nil => intro candidate member; simp [candidates] at member
  | cons active actives induction =>
      cases blocks with
      | nil => intro candidate member; simp [candidates] at member
      | cons block blocks =>
          intro candidate member
          rw [candidates] at member
          rcases List.mem_append.mp member with headMember | tailMember
          · rcases List.mem_map.mp headMember with
              ⟨template, templateMember, rfl⟩
            exact Template.activate_supported_eq_isSome
              template active
              (supportedTrue template (by simp [templateMember]))
          · exact induction blocks
              (by
                intro template templateMember
                exact supportedTrue template (by simp [templateMember]))
              candidate tailMember

/-- The same activity equation lifts across an item-indexed flat map. -/
theorem flatMap_candidates_supported_eq_isSome
    (items : List Item) (block : Item → List (Candidate Value))
    (correct : ∀ item ∈ items, ∀ candidate ∈ block item,
      candidate.supported = candidate.value.isSome) :
    ∀ candidate ∈ items.flatMap block,
      candidate.supported = candidate.value.isSome := by
  intro candidate member
  rw [List.mem_flatMap] at member
  rcases member with ⟨item, itemMember, candidateMember⟩
  exact correct item itemMember candidate candidateMember

end LeanTrominoes.PaddedSupportedCandidateBlocks
