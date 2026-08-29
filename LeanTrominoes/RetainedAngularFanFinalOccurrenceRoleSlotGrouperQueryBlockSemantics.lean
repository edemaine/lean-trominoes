/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperData

/-! # Query-block semantics of final occurrence-slot grouping -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotGrouper

open PeriodicEightOccurrenceSplit

/-- Grouping query-aligned nonempty width-three slot blocks yields exactly
one packed slot input per query.  This isolates the family-presentation list
arithmetic from the geometric stable-rank semantics. -/
theorem slotInputsOfQueries_map_flatMap
    {Clause : Type*}
    (clauses : List Clause)
    (query : Clause → Query)
    (slotBlock : Clause → List Slot)
    (blocksNonempty : ∀ clause ∈ clauses, slotBlock clause ≠ [])
    (blocksWidth : ∀ clause ∈ clauses, (slotBlock clause).length ≤ 3)
    (queryArityEq : ∀ clause ∈ clauses,
      queryArity (query clause) = (slotBlock clause).length) :
    slotInputsOfQueries
        (clauses.map query) (clauses.flatMap slotBlock) =
      clauses.map fun clause =>
        (query clause,
          RetainedDirectClauseOccurrenceSlots.ofList (slotBlock clause)) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have headMember : clause ∈ clause :: clauses := by simp
      have headNonempty := blocksNonempty clause headMember
      have headWidth := blocksWidth clause headMember
      have headArity := queryArityEq clause headMember
      have tailNonempty :
          ∀ tailClause ∈ clauses, slotBlock tailClause ≠ [] := by
        intro tailClause tailMember
        exact blocksNonempty tailClause (by simp [tailMember])
      have tailWidth :
          ∀ tailClause ∈ clauses,
            (slotBlock tailClause).length ≤ 3 := by
        intro tailClause tailMember
        exact blocksWidth tailClause (by simp [tailMember])
      have tailArity :
          ∀ tailClause ∈ clauses,
            queryArity (query tailClause) =
              (slotBlock tailClause).length := by
        intro tailClause tailMember
        exact queryArityEq tailClause (by simp [tailMember])
      cases blockEq : slotBlock clause with
      | nil => exact (headNonempty blockEq).elim
      | cons first rest =>
          cases rest with
          | nil =>
              have arityOne : queryArity (query clause) = 1 := by
                simpa [blockEq] using headArity
              simp only [List.map_cons, List.flatMap_cons, blockEq,
                slotInputsOfQueries, arityOne,
                List.cons_append, List.nil_append]
              rw [induction tailNonempty tailWidth tailArity]
              rfl
          | cons second rest =>
              cases rest with
              | nil =>
                  have arityTwo : queryArity (query clause) = 2 := by
                    simpa [blockEq] using headArity
                  simp only [List.map_cons, List.flatMap_cons, blockEq,
                    slotInputsOfQueries, arityTwo,
                    List.cons_append, List.nil_append]
                  rw [induction tailNonempty tailWidth tailArity]
                  rfl
              | cons third rest =>
                  cases rest with
                  | nil =>
                      have arityThree : queryArity (query clause) = 3 := by
                        simpa [blockEq] using headArity
                      simp only [List.map_cons, List.flatMap_cons, blockEq,
                        slotInputsOfQueries, arityThree,
                        List.cons_append, List.nil_append]
                      rw [induction tailNonempty tailWidth tailArity]
                      rfl
                  | cons fourth rest =>
                      simp [blockEq] at headWidth
                      omega

end LeanTrominoes.FinalOccurrenceRoleSlotGrouper

end
