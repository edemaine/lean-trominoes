/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Support semantics of fixed candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Correct support tags are closed under concatenating candidate streams. -/
theorem correctSupport_append
    (base : List Value) (first second : List (Candidate Value))
    (firstCorrect : CorrectSupport base first)
    (secondCorrect : CorrectSupport base second) :
    CorrectSupport base (first ++ second) := by
  intro candidate member
  rcases List.mem_append.mp member with member | member
  · exact firstCorrect candidate member
  · exact secondCorrect candidate member

/-- Activating one correctly tagged template block preserves exact support;
an inactive block consists entirely of rejected `none` slots. -/
theorem correctSupport_map_activate
    (base : List Value) (block : List (Template Value))
    (correct : ∀ template ∈ block,
      template.supported = decide (template.value ∈ base))
    (active : Bool) :
    CorrectSupport base (block.map (Template.activate active)) := by
  intro candidate member
  rcases List.mem_map.mp member with ⟨template, templateMember, rfl⟩
  cases active <;>
    simp [Template.activate, correct template templateMember]

/-- Inactive blocks require no payload support proof, while active blocks use
the pointwise template invariant. -/
theorem correctSupport_map_activate_of_active
    (base : List Value) (block : List (Template Value)) (active : Bool)
    (correct : if active then
        ∀ template ∈ block,
          template.supported = decide (template.value ∈ base)
      else True) :
    CorrectSupport base (block.map (Template.activate active)) := by
  cases active with
  | false =>
      intro candidate member
      rcases List.mem_map.mp member with ⟨template, _templateMember, rfl⟩
      simp [Template.activate]
  | true =>
      exact correctSupport_map_activate base block (by simpa using correct) true

/-- Predicate activation of a correctly tagged fixed block family produces
a correctly support-guarded padded candidate stream. -/
theorem correctSupport_candidates
    (base : List Value) (actives : List Bool)
    (blocks : List (List (Template Value)))
    (correct : CorrectTemplates base blocks) :
    CorrectSupport base (candidates actives blocks) := by
  induction actives generalizing blocks with
  | nil => intro candidate member; simp [candidates] at member
  | cons active actives induction =>
      cases blocks with
      | nil => intro candidate member; simp [candidates] at member
      | cons block blocks =>
          have headCorrect : ∀ template ∈ block,
              template.supported = decide (template.value ∈ base) := by
            intro template templateMember
            exact correct template (by simp [templateMember])
          have tailCorrect : CorrectTemplates base blocks := by
            intro template templateMember
            exact correct template (by simp [templateMember])
          rw [candidates]
          exact correctSupport_append base _ _
            (correctSupport_map_activate base block headCorrect active)
            (induction blocks tailCorrect)

/-- The activation-sensitive invariant is sufficient for the complete padded
candidate stream. -/
theorem correctSupport_candidates_of_active
    (base : List Value) (actives : List Bool)
    (blocks : List (List (Template Value)))
    (correct : CorrectActiveTemplates base actives blocks) :
    CorrectSupport base (candidates actives blocks) := by
  induction actives generalizing blocks with
  | nil => intro candidate member; simp [candidates] at member
  | cons active actives induction =>
      cases blocks with
      | nil => intro candidate member; simp [candidates] at member
      | cons block blocks =>
          rw [candidates]
          exact correctSupport_append base _ _
            (correctSupport_map_activate_of_active
              base block active correct.1)
            (induction blocks correct.2)

end LeanTrominoes.PaddedSupportedCandidateBlocks
