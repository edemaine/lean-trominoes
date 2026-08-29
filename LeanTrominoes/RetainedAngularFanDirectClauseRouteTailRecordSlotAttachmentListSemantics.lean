/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachment
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates

/-! # List semantics of direct route-tail slot attachment -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF

@[simp] theorem
    retainedDirectClauseRouteTailRecordQueryOfSlotInput_precomputed
    (token : FormulaShapeDirectionOrdering.Token)
    (slots : RetainedDirectClauseOccurrenceSlots) :
    retainedDirectClauseRouteTailRecordQueryOfSlotInput
        (.precomputed token, slots) = none := by
  rfl

@[simp] theorem retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_append
    (first second : List RetainedDirectClauseRouteTailRecordSlotInput) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (first ++ second) =
      retainedDirectClauseRouteTailRecordQueriesOfSlotInputs first ++
        retainedDirectClauseRouteTailRecordQueriesOfSlotInputs second := by
  simp [retainedDirectClauseRouteTailRecordQueriesOfSlotInputs]

theorem retainedFinalPrecomputedClauseQueries_eq_map
    (tokens : List FormulaShapeDirectionOrdering.Token) :
    retainedFinalPrecomputedClauseQueries tokens =
      tokens.map RetainedFinalCopiedClauseQuery.precomputed := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp only [retainedFinalPrecomputedClauseQueries, List.flatMap_cons,
        retainedFinalPrecomputedClauseQueryBlock, List.singleton_append,
        List.map_cons, List.cons.injEq, true_and]
      exact induction

/-- Carrier and bend wrapper queries never produce direct route-tail
records, regardless of the aligned slot list. -/
theorem retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_zip_precomputed
    (tokens : List FormulaShapeDirectionOrdering.Token)
    (slots : List RetainedDirectClauseOccurrenceSlots) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (List.zip (retainedFinalPrecomputedClauseQueries tokens) slots) =
      [] := by
  rw [retainedFinalPrecomputedClauseQueries_eq_map]
  induction tokens generalizing slots with
  | nil => rfl
  | cons token tokens induction =>
      cases slots with
      | nil => rfl
      | cons slot slots =>
          simp only [List.map_cons, List.zip_cons_cons,
            retainedDirectClauseRouteTailRecordQueriesOfSlotInputs,
            List.flatMap_cons,
            retainedDirectClauseRouteTailRecordQueryOfSlotInput_precomputed,
            Option.toList_none, List.nil_append]
          exact induction slots

end PeriodicEightOccurrenceSplit
end LeanTrominoes
