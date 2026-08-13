/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicCNFDeduplication

/-!
# Deduplicating positioned periodic clauses

A finite neighboring-block construction can contain several translated
representatives of the same periodic protoclause.  Those copies are useful
while assembling the finite block, but retaining them as separate periodic
clause vertices would create coincident incidence gadgets.

This file keeps one positioned representative of each erased literal list.
Because a CNF is a conjunction, removing duplicate clauses preserves its
assignment semantics exactly.  Locality and clause width are likewise
unchanged.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Choose the position of the first source occurrence of an erased
protoclauses, with the usual harmless total default outside the source
presentation. -/
def representativeClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clause : PeriodicClause Variable) : Cell :=
  source.clausePosition (source.erase.clauses.idxOf clause)

/-- Keep one positioned representative of every distinct erased literal
list.  `List.dedup` fixes the resulting periodic clause order. -/
def deduplicateByLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF Variable :=
  ⟨source.erase.clauses.dedup.map fun clause =>
    ⟨source.representativeClausePosition clause, clause⟩⟩

/-- Positioned clause deduplication produces no duplicate positioned
clauses, because projecting literals recovers the duplicate-free erased
clause list. -/
theorem deduplicateByLiterals_clauses_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.clauses.Nodup := by
  unfold deduplicateByLiterals
  apply source.erase.clauses.nodup_dedup.map_on
  intro first _ second _ equal
  exact congrArg PositionedPeriodicClause.literals equal

/-- Erasing the positioned deduplication is exactly ordinary list
deduplication of the periodic clauses. -/
@[simp]
theorem erase_deduplicateByLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.erase =
      source.erase.deduplicate := by
  simp [deduplicateByLiterals, erase,
    PeriodicCNF.deduplicate,
    List.map_map, Function.comp_def]

/-- Deduplication retains precisely the original erased protoclauses. -/
@[simp]
theorem clause_mem_erase_deduplicateByLiterals_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clause : PeriodicClause Variable) :
    clause ∈ source.deduplicateByLiterals.erase.clauses ↔
      clause ∈ source.erase.clauses := by
  simp

/-- An assignment satisfies the deduplicated positioned formula exactly when
it satisfies the original erased formula. -/
@[simp]
theorem deduplicateByLiterals_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    source.deduplicateByLiterals.erase.Satisfies assignment ↔
      source.erase.Satisfies assignment := by
  rw [erase_deduplicateByLiterals]
  exact source.erase.deduplicate_satisfies_iff assignment

/-- Removing duplicate positioned protoclauses preserves periodic
satisfiability. -/
@[simp]
theorem deduplicateByLiterals_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.erase.Satisfiable ↔
      source.erase.Satisfiable := by
  rw [erase_deduplicateByLiterals]
  exact source.erase.deduplicate_satisfiable_iff

/-- Clause locality is insensitive to duplicate removal. -/
@[simp]
theorem deduplicateByLiterals_isLocal_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.erase.IsLocal ↔
      source.erase.IsLocal := by
  rw [erase_deduplicateByLiterals]
  exact source.erase.deduplicate_isLocal_iff

/-- Every clause-width bound is insensitive to duplicate removal. -/
@[simp]
theorem deduplicateByLiterals_widthAtMost_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (width : Nat) :
    source.deduplicateByLiterals.erase.WidthAtMost width ↔
      source.erase.WidthAtMost width := by
  rw [erase_deduplicateByLiterals]
  exact source.erase.deduplicate_widthAtMost_iff width

end PositionedPeriodicCNF
end LeanTrominoes
