/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleSemantics
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperData

/-! # Correctness of final occurrence-role/slot grouping -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotGrouper

open PeriodicEightOccurrenceSplit

private theorem queryArity_le_three (query : Query) :
    queryArity query ≤ 3 := by
  cases query with
  | precomputed token =>
      cases token with
      | clause profile => cases profile <;>
          simp [queryArity, retainedFinalCopiedClauseQueryArity]
      | _ => simp [queryArity, retainedFinalCopiedClauseQueryArity]
  | unary => simp [queryArity, retainedFinalCopiedClauseQueryArity]
  | binary => simp [queryArity, retainedFinalCopiedClauseQueryArity]
  | ternary => simp [queryArity, retainedFinalCopiedClauseQueryArity]

private theorem scan_query_zero
    (query : Query)
    (arity : queryArity query = 0) :
    FiniteStateTransducer.scan transition none
        (List.zip
          (retainedFinalCopiedClauseOccurrenceRolesOfQuery query) []) =
      (none, []) := by
  have retainedArity : retainedFinalCopiedClauseQueryArity query = 0 := by
    simpa only [queryArity] using arity
  have rolesEq :
      retainedFinalCopiedClauseOccurrenceRolesOfQuery query = [] := by
    simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery,
      retainedArity, List.take_zero, List.map_nil]
  rw [rolesEq]
  rfl

private theorem scan_query_one
    (query : Query) (first : Slot)
    (arity : queryArity query = 1) :
    FiniteStateTransducer.scan transition none
        (List.zip
          (retainedFinalCopiedClauseOccurrenceRolesOfQuery query)
          [first]) =
      (none, [(query, .unary first)]) := by
  have retainedArity : retainedFinalCopiedClauseQueryArity query = 1 := by
    simpa only [queryArity] using arity
  have rolesEq :
      retainedFinalCopiedClauseOccurrenceRolesOfQuery query =
        [(query, 0)] := by
    simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery,
      retainedArity, List.finRange_succ, List.finRange_zero,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
  rw [rolesEq]
  simp [FiniteStateTransducer.scan, transition, arity]

private theorem scan_query_two
    (query : Query) (first second : Slot)
    (arity : queryArity query = 2) :
    FiniteStateTransducer.scan transition none
        (List.zip
          (retainedFinalCopiedClauseOccurrenceRolesOfQuery query)
          [first, second]) =
      (none, [(query, .binary first second)]) := by
  have retainedArity : retainedFinalCopiedClauseQueryArity query = 2 := by
    simpa only [queryArity] using arity
  have rolesEq :
      retainedFinalCopiedClauseOccurrenceRolesOfQuery query =
        [(query, 0), (query, 1)] := by
    have one : Fin.succ (0 : Fin 2) = (1 : Fin 3) := by
      apply Fin.ext
      rfl
    simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery,
      retainedArity, List.finRange_succ, List.finRange_zero,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, one]
  rw [rolesEq]
  simp [FiniteStateTransducer.scan, transition, arity]

private theorem scan_query_three
    (query : Query) (first second third : Slot)
    (arity : queryArity query = 3) :
    FiniteStateTransducer.scan transition none
        (List.zip
          (retainedFinalCopiedClauseOccurrenceRolesOfQuery query)
          [first, second, third]) =
      (none, [(query, .ternary first second third)]) := by
  have retainedArity : retainedFinalCopiedClauseQueryArity query = 3 := by
    simpa only [queryArity] using arity
  have rolesEq :
      retainedFinalCopiedClauseOccurrenceRolesOfQuery query =
        [(query, 0), (query, 1), (query, 2)] := by
    have one : Fin.succ (0 : Fin 2) = (1 : Fin 3) := by
      apply Fin.ext
      rfl
    have two : (Fin.succ (0 : Fin 1)).succ = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery,
      retainedArity, List.finRange_succ, List.finRange_zero,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      one, two]
  rw [rolesEq]
  simp [FiniteStateTransducer.scan, transition, arity]

/-- Scanning a canonical expanded role stream with an equally long slot
stream realizes the declarative per-query slot grouping exactly. -/
theorem scan_zip_occurrenceRoles
    (queries : List Query) (slots : List Slot)
    (lengthEq :
      (retainedFinalCopiedClauseOccurrenceRoles queries).length =
        slots.length) :
    FiniteStateTransducer.scan transition none
        (List.zip
          (retainedFinalCopiedClauseOccurrenceRoles queries) slots) =
      (none, slotInputsOfQueries queries slots) := by
  induction queries generalizing slots with
  | nil =>
      have slotsNil : slots = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [retainedFinalCopiedClauseOccurrenceRoles,
          List.flatMap_nil, List.length_nil] using lengthEq.symm
      subst slots
      rfl
  | cons query queries induction =>
      have arityCases :
          queryArity query = 0 ∨
          queryArity query = 1 ∨
          queryArity query = 2 ∨
          queryArity query = 3 := by
        have := queryArity_le_three query
        omega
      rcases arityCases with arity | arity | arity | arity
      · have retainedArity :
            retainedFinalCopiedClauseQueryArity query = 0 := by
          simpa only [queryArity] using arity
        have headNil :
            retainedFinalCopiedClauseOccurrenceRolesOfQuery query = [] :=
          List.eq_nil_of_length_eq_zero (by
            rw [retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
              retainedArity])
        have tailLength :
            (retainedFinalCopiedClauseOccurrenceRoles queries).length =
              slots.length := by
          change
            (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
              retainedFinalCopiedClauseOccurrenceRoles queries).length =
                slots.length at lengthEq
          rw [headNil, List.nil_append] at lengthEq
          exact lengthEq
        have groupedEq :
            slotInputsOfQueries (query :: queries) slots =
              slotInputsOfQueries queries slots := by
          simp only [slotInputsOfQueries, arity]
        rw [groupedEq]
        change FiniteStateTransducer.scan transition none
            (List.zip
              (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                retainedFinalCopiedClauseOccurrenceRoles queries) slots) = _
        rw [headNil, List.nil_append, induction slots tailLength]
      · cases slots with
        | nil =>
            change
              (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                retainedFinalCopiedClauseOccurrenceRoles queries).length =
                  0 at lengthEq
            have retainedArity :
                retainedFinalCopiedClauseQueryArity query = 1 := by
              simpa only [queryArity] using arity
            rw [List.length_append,
              retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
              retainedArity] at lengthEq
            omega
        | cons first slots =>
            have retainedArity :
                retainedFinalCopiedClauseQueryArity query = 1 := by
              simpa only [queryArity] using arity
            have tailLength :
                (retainedFinalCopiedClauseOccurrenceRoles queries).length =
                  slots.length := by
              change
                (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                  retainedFinalCopiedClauseOccurrenceRoles queries).length =
                    (first :: slots).length at lengthEq
              rw [List.length_append,
                retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                retainedArity, List.length_cons] at lengthEq
              omega
            have groupedEq :
                slotInputsOfQueries (query :: queries) (first :: slots) =
                  (query, .unary first) ::
                    slotInputsOfQueries queries slots := by
              simp only [slotInputsOfQueries, arity]
            rw [groupedEq]
            change FiniteStateTransducer.scan transition none
                (List.zip
                  (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                    retainedFinalCopiedClauseOccurrenceRoles queries)
                  ([first] ++ slots)) = _
            rw [List.zip_append (by
                simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                  retainedArity, List.length_cons, List.length_nil]),
              FiniteStateTransducer.scan_append,
              scan_query_one query first arity]
            simp only
            rw [induction slots tailLength]
            rfl
      · cases slots with
        | nil =>
            change
              (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                retainedFinalCopiedClauseOccurrenceRoles queries).length =
                  0 at lengthEq
            have retainedArity :
                retainedFinalCopiedClauseQueryArity query = 2 := by
              simpa only [queryArity] using arity
            rw [List.length_append,
              retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
              retainedArity] at lengthEq
            omega
        | cons first slots =>
            have retainedArity :
                retainedFinalCopiedClauseQueryArity query = 2 := by
              simpa only [queryArity] using arity
            cases slots with
            | nil =>
                change
                  (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                    retainedFinalCopiedClauseOccurrenceRoles queries).length =
                      1 at lengthEq
                rw [List.length_append,
                  retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                  retainedArity] at lengthEq
                omega
            | cons second slots =>
                have tailLength :
                    (retainedFinalCopiedClauseOccurrenceRoles queries).length =
                      slots.length := by
                  change
                    (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                      retainedFinalCopiedClauseOccurrenceRoles queries).length =
                        (first :: second :: slots).length at lengthEq
                  rw [List.length_append,
                    retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                    retainedArity, List.length_cons] at lengthEq
                  simp only [List.length_cons] at lengthEq
                  omega
                have groupedEq :
                    slotInputsOfQueries (query :: queries)
                        (first :: second :: slots) =
                      (query, .binary first second) ::
                        slotInputsOfQueries queries slots := by
                  simp only [slotInputsOfQueries, arity]
                rw [groupedEq]
                change FiniteStateTransducer.scan transition none
                    (List.zip
                      (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                        retainedFinalCopiedClauseOccurrenceRoles queries)
                      ([first, second] ++ slots)) = _
                rw [List.zip_append (by
                    simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                      retainedArity, List.length_cons, List.length_nil]),
                  FiniteStateTransducer.scan_append,
                  scan_query_two query first second arity]
                simp only
                rw [induction slots tailLength]
                rfl
      · cases slots with
        | nil =>
            change
              (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                retainedFinalCopiedClauseOccurrenceRoles queries).length =
                  0 at lengthEq
            have retainedArity :
                retainedFinalCopiedClauseQueryArity query = 3 := by
              simpa only [queryArity] using arity
            rw [List.length_append,
              retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
              retainedArity] at lengthEq
            omega
        | cons first slots =>
            have retainedArity :
                retainedFinalCopiedClauseQueryArity query = 3 := by
              simpa only [queryArity] using arity
            cases slots with
            | nil =>
                change
                  (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                    retainedFinalCopiedClauseOccurrenceRoles queries).length =
                      1 at lengthEq
                rw [List.length_append,
                  retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                  retainedArity] at lengthEq
                omega
            | cons second slots =>
                cases slots with
                | nil =>
                    change
                      (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                        retainedFinalCopiedClauseOccurrenceRoles queries).length =
                          2 at lengthEq
                    rw [List.length_append,
                      retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                      retainedArity] at lengthEq
                    omega
                | cons third slots =>
                    have tailLength :
                        (retainedFinalCopiedClauseOccurrenceRoles queries).length =
                          slots.length := by
                      change
                        (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                          retainedFinalCopiedClauseOccurrenceRoles queries).length =
                            (first :: second :: third :: slots).length at lengthEq
                      rw [List.length_append,
                        retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                        retainedArity, List.length_cons] at lengthEq
                      simp only [List.length_cons] at lengthEq
                      omega
                    have groupedEq :
                        slotInputsOfQueries (query :: queries)
                            (first :: second :: third :: slots) =
                          (query, .ternary first second third) ::
                            slotInputsOfQueries queries slots := by
                      simp only [slotInputsOfQueries, arity]
                    rw [groupedEq]
                    change FiniteStateTransducer.scan transition none
                        (List.zip
                          (retainedFinalCopiedClauseOccurrenceRolesOfQuery query ++
                            retainedFinalCopiedClauseOccurrenceRoles queries)
                          ([first, second, third] ++ slots)) = _
                    rw [List.zip_append (by
                        simp only [retainedFinalCopiedClauseOccurrenceRolesOfQuery_length,
                          retainedArity, List.length_cons, List.length_nil]),
                      FiniteStateTransducer.scan_append,
                      scan_query_three query first second third arity]
                    simp only
                    rw [induction slots tailLength]
                    rfl

/-- The complete finite-state output is the declarative grouping. -/
theorem slotInputs_zip_occurrenceRoles
    (queries : List Query) (slots : List Slot)
    (lengthEq :
      (retainedFinalCopiedClauseOccurrenceRoles queries).length =
        slots.length) :
    slotInputs
        (List.zip
          (retainedFinalCopiedClauseOccurrenceRoles queries) slots) =
      slotInputsOfQueries queries slots := by
  simp [slotInputs, FiniteStateTransducer.output,
    scan_zip_occurrenceRoles queries slots lengthEq, finish]

end LeanTrominoes.FinalOccurrenceRoleSlotGrouper

end
