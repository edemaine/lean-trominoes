/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrences
import LeanTrominoes.PeriodicThreeSATThreeSize
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # Exact presentation size of occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

theorem occurrenceVariables_length_eq_count {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) :
    (occurrenceVariables source atom).length =
      ((taggedLiterals source).map fun tagged => tagged.1.atom).count atom := by
  unfold occurrenceVariables
  induction taggedLiterals source with
  | nil => simp
  | cons tagged rest induction =>
      by_cases same : tagged.1.atom = atom
      · simp [same, induction]
      · simp [same, induction]

/-- Occurrence lists partition the tagged source literals exactly. -/
theorem occurrenceVariables_total_length {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    ((sourceVariables source).map fun atom =>
      (occurrenceVariables source atom).length).sum =
        (taggedLiterals source).length := by
  rw [show sourceVariables source =
      ((taggedLiterals source).map fun tagged => tagged.1.atom).dedup by
    rfl]
  simp_rw [occurrenceVariables_length_eq_count]
  simpa using List.sum_map_count_dedup_eq_length
    ((taggedLiterals source).map fun tagged => tagged.1.atom)

@[simp] theorem cycleClauses_length {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    (cycleClauses copies).length = copies.length := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      simp only [cycleClauses, List.length_cons]
      rw [cycleFrom_length]

/-- There is exactly one implication clause per source literal occurrence. -/
@[simp] theorem allCycleClauses_length {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (allCycleClauses source).length =
      PeriodicCNF.presentationLiteralCount source := by
  unfold allCycleClauses
  rw [List.length_flatMap]
  simp_rw [cycleClauses_length]
  rw [occurrenceVariables_total_length, taggedLiterals_length]

@[simp] theorem occurrenceClauses_length {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (occurrenceClauses source).length = source.clauses.length := by
  simp [occurrenceClauses]

/-- Occurrence splitting adds exactly one implication clause per source
literal. -/
@[simp] theorem formula_clauses_length {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (formula source).clauses.length =
      source.clauses.length +
        PeriodicCNF.presentationLiteralCount source := by
  simp [formula]

theorem cycleFrom_presentationLiteralCount {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    PeriodicCNF.presentationLiteralCount
        ⟨cycleFrom first current rest⟩ =
      2 * (rest.length + 1) := by
  induction rest generalizing current with
  | nil =>
      simp [cycleFrom, PeriodicCNF.presentationLiteralCount,
        implicationClause]
  | cons next rest induction =>
      simp only [cycleFrom, PeriodicCNF.presentationLiteralCount,
        List.flatten_cons, List.length_append, implicationClause,
        List.length_cons, List.length_nil]
      rw [show (List.flatten (cycleFrom first next rest)).length =
          2 * (rest.length + 1) by
        exact induction next]
      omega

@[simp] theorem cycleClauses_presentationLiteralCount
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    PeriodicCNF.presentationLiteralCount ⟨cycleClauses copies⟩ =
      2 * copies.length := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      rw [cycleClauses]
      rw [cycleFrom_presentationLiteralCount]
      simp only [List.length_cons]

theorem cyclesFor_presentationLiteralCount {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atoms : List Variable) :
    PeriodicCNF.presentationLiteralCount
        ⟨atoms.flatMap fun atom =>
          cycleClauses (occurrenceVariables source atom)⟩ =
      2 * ((atoms.map fun atom =>
        (occurrenceVariables source atom).length).sum) := by
  induction atoms with
  | nil => simp [PeriodicCNF.presentationLiteralCount]
  | cons atom atoms induction =>
      simp only [List.flatMap_cons, PeriodicCNF.presentationLiteralCount,
        List.flatten_append, List.length_append, List.map_cons,
        List.sum_cons]
      rw [show (List.flatten
          (cycleClauses (occurrenceVariables source atom))).length =
            2 * (occurrenceVariables source atom).length by
          exact cycleClauses_presentationLiteralCount _]
      rw [show (List.flatten
          (atoms.flatMap fun atom =>
            cycleClauses (occurrenceVariables source atom))).length =
            2 * ((atoms.map fun atom =>
              (occurrenceVariables source atom).length).sum) by
          exact induction]
      omega

/-- The implication cycles contain exactly two literal occurrences per
source occurrence. -/
@[simp] theorem allCycleClauses_presentationLiteralCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.presentationLiteralCount ⟨allCycleClauses source⟩ =
      2 * PeriodicCNF.presentationLiteralCount source := by
  unfold allCycleClauses
  rw [cyclesFor_presentationLiteralCount]
  rw [occurrenceVariables_total_length, taggedLiterals_length]

theorem presentationLiteralCount_append {Variable : Type*}
    (first second : List (PeriodicClause Variable)) :
    PeriodicCNF.presentationLiteralCount ⟨first ++ second⟩ =
      PeriodicCNF.presentationLiteralCount ⟨first⟩ +
        PeriodicCNF.presentationLiteralCount ⟨second⟩ := by
  simp [PeriodicCNF.presentationLiteralCount]

/-- The copied source clauses contribute once and the implication cycles
twice, for exactly three output literal occurrences per source occurrence. -/
@[simp] theorem formula_presentationLiteralCount {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    PeriodicCNF.presentationLiteralCount (formula source) =
      3 * PeriodicCNF.presentationLiteralCount source := by
  have occurrenceCount :
      PeriodicCNF.presentationLiteralCount
          ⟨occurrenceClauses source⟩ =
        PeriodicCNF.presentationLiteralCount source := by
    have lengthEq := congrArg List.length
      (occurrenceClauses_variableOccurrences source)
    rw [PeriodicCNF.variableOccurrences_length] at lengthEq
    simpa [allOccurrenceVariables, taggedLiterals_length] using lengthEq
  calc
    PeriodicCNF.presentationLiteralCount (formula source) =
        PeriodicCNF.presentationLiteralCount ⟨occurrenceClauses source⟩ +
          PeriodicCNF.presentationLiteralCount
            ⟨allCycleClauses source⟩ := by
      unfold formula
      exact presentationLiteralCount_append _ _
    _ = 3 * PeriodicCNF.presentationLiteralCount source := by
      rw [occurrenceCount,
        allCycleClauses_presentationLiteralCount]
      omega

end PeriodicThreeSATThree
end LeanTrominoes
