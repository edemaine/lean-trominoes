/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperData

/-! # List-block semantics of final occurrence-slot grouping -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotGrouper

open PeriodicEightOccurrenceSplit

/-- Grouping equally indexed query and slot-block lists is their pointwise
zip, provided every block is nonempty, has width at most three, and has the
arity declared by its query. -/
theorem slotInputsOfQueries_flatten_blocks
    (queries : List Query)
    (blocks : List (List Slot))
    (lengthEq : queries.length = blocks.length)
    (blocksNonempty : ∀ block ∈ blocks, block ≠ [])
    (blocksWidth : ∀ block ∈ blocks, block.length ≤ 3)
    (aritiesEq : queries.map queryArity = blocks.map List.length) :
    slotInputsOfQueries queries blocks.flatten =
      List.zip queries
        (blocks.map RetainedDirectClauseOccurrenceSlots.ofList) := by
  induction queries generalizing blocks with
  | nil =>
      have blocksNil : blocks = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using lengthEq.symm
      subst blocks
      rfl
  | cons query queries induction =>
      cases blocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          have headNonempty : block ≠ [] :=
            blocksNonempty block (by simp)
          have headWidth : block.length ≤ 3 :=
            blocksWidth block (by simp)
          have tailNonempty : ∀ tailBlock ∈ blocks,
              tailBlock ≠ [] := by
            intro tailBlock tailMember
            exact blocksNonempty tailBlock (by simp [tailMember])
          have tailWidth : ∀ tailBlock ∈ blocks,
              tailBlock.length ≤ 3 := by
            intro tailBlock tailMember
            exact blocksWidth tailBlock (by simp [tailMember])
          have tailLength : queries.length = blocks.length := by
            simpa using lengthEq
          have headArity : queryArity query = block.length := by
            simpa using congrArg List.head? aritiesEq
          have tailArities : queries.map queryArity =
              blocks.map List.length := by
            simpa using congrArg List.tail aritiesEq
          cases blockEq : block with
          | nil => exact (headNonempty blockEq).elim
          | cons first rest =>
              cases rest with
              | nil =>
                  have arityOne : queryArity query = 1 := by
                    simpa [blockEq] using headArity
                  simp only [List.flatten_cons,
                    List.cons_append, List.nil_append,
                    slotInputsOfQueries, arityOne, List.map_cons,
                    List.zip_cons_cons]
                  rw [induction blocks tailLength tailNonempty tailWidth
                    tailArities]
                  rfl
              | cons second rest =>
                  cases rest with
                  | nil =>
                      have arityTwo : queryArity query = 2 := by
                        simpa [blockEq] using headArity
                      simp only [List.flatten_cons,
                        List.cons_append, List.nil_append,
                        slotInputsOfQueries, arityTwo, List.map_cons,
                        List.zip_cons_cons]
                      rw [induction blocks tailLength tailNonempty tailWidth
                        tailArities]
                      rfl
                  | cons third rest =>
                      cases rest with
                      | nil =>
                          have arityThree : queryArity query = 3 := by
                            simpa [blockEq] using headArity
                          simp only [List.flatten_cons,
                            List.cons_append, List.nil_append,
                            slotInputsOfQueries, arityThree, List.map_cons,
                            List.zip_cons_cons]
                          rw [induction blocks tailLength tailNonempty
                            tailWidth tailArities]
                          rfl
                      | cons fourth rest =>
                          simp [blockEq] at headWidth
                          omega

end LeanTrominoes.FinalOccurrenceRoleSlotGrouper

end
