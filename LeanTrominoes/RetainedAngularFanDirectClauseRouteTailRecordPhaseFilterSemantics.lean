/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter

/-! # Semantics of direct clause route-tail phase filters -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

private theorem filterSlotInputs_zip_eq_self
    (predicate : RetainedFinalCopiedClauseQuery → Bool)
    (queries : List RetainedFinalCopiedClauseQuery)
    (slots : List RetainedDirectClauseOccurrenceSlots)
    (selected : ∀ query ∈ queries, predicate query = true) :
    (List.zip queries slots).flatMap (fun input =>
        if predicate input.1 then [input] else []) =
      List.zip queries slots := by
  induction queries generalizing slots with
  | nil => rfl
  | cons query queries induction =>
      cases slots with
      | nil => rfl
      | cons slot slots =>
          have headSelected : predicate query = true :=
            selected query (by simp)
          have tailSelected : ∀ tailQuery ∈ queries,
              predicate tailQuery = true := by
            intro tailQuery tailMember
            exact selected tailQuery (by simp [tailMember])
          simp only [List.zip_cons_cons, List.flatMap_cons,
            headSelected, if_true, List.singleton_append,
            List.cons.injEq, true_and]
          exact induction slots tailSelected

private theorem filterSlotInputs_zip_eq_nil
    (predicate : RetainedFinalCopiedClauseQuery → Bool)
    (queries : List RetainedFinalCopiedClauseQuery)
    (slots : List RetainedDirectClauseOccurrenceSlots)
    (rejected : ∀ query ∈ queries, predicate query = false) :
    (List.zip queries slots).flatMap (fun input =>
        if predicate input.1 then [input] else []) = [] := by
  induction queries generalizing slots with
  | nil => rfl
  | cons query queries induction =>
      cases slots with
      | nil => rfl
      | cons slot slots =>
          have headRejected : predicate query = false :=
            rejected query (by simp)
          have tailRejected : ∀ tailQuery ∈ queries,
              predicate tailQuery = false := by
            intro tailQuery tailMember
            exact rejected tailQuery (by simp [tailMember])
          simp only [List.zip_cons_cons, List.flatMap_cons,
            headRejected, if_false, List.nil_append]
          exact induction slots tailRejected

theorem retainedDirectCrossoverRouteTailRecordSlotInputs_zip_eq_self
    (queries : List RetainedFinalCopiedClauseQuery)
    (slots : List RetainedDirectClauseOccurrenceSlots)
    (selected : ∀ query ∈ queries,
      query.isDirectCrossover = true) :
    retainedDirectCrossoverRouteTailRecordSlotInputs
        (List.zip queries slots) =
      List.zip queries slots := by
  exact filterSlotInputs_zip_eq_self
    RetainedFinalCopiedClauseQuery.isDirectCrossover
    queries slots selected

theorem retainedDirectCrossoverRouteTailRecordSlotInputs_zip_eq_nil
    (queries : List RetainedFinalCopiedClauseQuery)
    (slots : List RetainedDirectClauseOccurrenceSlots)
    (rejected : ∀ query ∈ queries,
      query.isDirectCrossover = false) :
    retainedDirectCrossoverRouteTailRecordSlotInputs
        (List.zip queries slots) = [] := by
  exact filterSlotInputs_zip_eq_nil
    RetainedFinalCopiedClauseQuery.isDirectCrossover
    queries slots rejected

theorem retainedDirectRoutedRouteTailRecordSlotInputs_zip_eq_self
    (queries : List RetainedFinalCopiedClauseQuery)
    (slots : List RetainedDirectClauseOccurrenceSlots)
    (selected : ∀ query ∈ queries,
      query.isDirectRouted = true) :
    retainedDirectRoutedRouteTailRecordSlotInputs
        (List.zip queries slots) =
      List.zip queries slots := by
  exact filterSlotInputs_zip_eq_self
    RetainedFinalCopiedClauseQuery.isDirectRouted
    queries slots selected

theorem retainedDirectRoutedRouteTailRecordSlotInputs_zip_eq_nil
    (queries : List RetainedFinalCopiedClauseQuery)
    (slots : List RetainedDirectClauseOccurrenceSlots)
    (rejected : ∀ query ∈ queries,
      query.isDirectRouted = false) :
    retainedDirectRoutedRouteTailRecordSlotInputs
        (List.zip queries slots) = [] := by
  exact filterSlotInputs_zip_eq_nil
    RetainedFinalCopiedClauseQuery.isDirectRouted
    queries slots rejected

end PeriodicEightOccurrenceSplit
end LeanTrominoes
