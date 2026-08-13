/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOccurrences
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Flatten

/-!
# Deduplicating periodic CNF presentations

Repeated protoclauses impose the same translated constraint, so a periodic
CNF can retain one copy of each literal list without changing its semantics.
This normalization is useful when a finite neighboring-block construction
contains several representatives of one periodic clause orbit.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Remove repeated protoclauses from a finite periodic-CNF presentation. -/
def deduplicate {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : PeriodicCNF Variable :=
  ⟨source.clauses.dedup⟩

@[simp]
theorem deduplicate_clauses
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    source.deduplicate.clauses = source.clauses.dedup :=
  rfl

@[simp]
theorem mem_deduplicate_clauses_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause : PeriodicClause Variable) :
    clause ∈ source.deduplicate.clauses ↔
      clause ∈ source.clauses := by
  simp [deduplicate]

@[simp]
theorem deduplicate_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    source.deduplicate.Satisfies assignment ↔
      source.Satisfies assignment := by
  constructor
  · intro satisfies translate clause clauseMember
    exact satisfies translate clause
      ((mem_deduplicate_clauses_iff source clause).mpr clauseMember)
  · intro satisfies translate clause clauseMember
    exact satisfies translate clause
      ((mem_deduplicate_clauses_iff source clause).mp clauseMember)

@[simp]
theorem deduplicate_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    source.deduplicate.Satisfiable ↔ source.Satisfiable := by
  unfold Satisfiable
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨assignment,
        (source.deduplicate_satisfies_iff assignment).mp
          satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨assignment,
        (source.deduplicate_satisfies_iff assignment).mpr
          satisfies⟩

@[simp]
theorem deduplicate_isLocal_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    source.deduplicate.IsLocal ↔ source.IsLocal := by
  unfold IsLocal
  constructor
  · intro localProof clause clauseMember
    exact localProof clause
      ((mem_deduplicate_clauses_iff source clause).mpr clauseMember)
  · intro localProof clause clauseMember
    exact localProof clause
      ((mem_deduplicate_clauses_iff source clause).mp clauseMember)

@[simp]
theorem deduplicate_widthAtMost_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : Nat) :
    source.deduplicate.WidthAtMost width ↔
      source.WidthAtMost width := by
  unfold WidthAtMost
  constructor
  · intro bounded clause clauseMember
    exact bounded clause
      ((mem_deduplicate_clauses_iff source clause).mpr clauseMember)
  · intro bounded clause clauseMember
    exact bounded clause
      ((mem_deduplicate_clauses_iff source clause).mp clauseMember)

/-- Removing duplicate clauses removes, but never adds, literal
occurrences. -/
theorem deduplicate_variableOccurrences_sublist
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Sublist source.deduplicate.variableOccurrences
      source.variableOccurrences := by
  unfold variableOccurrences deduplicate
  exact (List.dedup_sublist source.clauses).flatMap
    (fun clause => clause.map PeriodicLiteral.atom)

/-- Every finite-presentation occurrence bound survives clause
deduplication. -/
theorem deduplicate_occurrencesAtMost
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (bound : Nat)
    (sourceOccurrences : source.OccurrencesAtMost bound) :
    source.deduplicate.OccurrencesAtMost bound := by
  intro atom
  exact
    ((deduplicate_variableOccurrences_sublist source).subperm.count_le
      atom).trans
        (sourceOccurrences atom)

end PeriodicCNF
end LeanTrominoes
