import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import Mathlib.Data.List.Dedup

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

/-- Erasing the positioned deduplication is exactly ordinary list
deduplication of the periodic clauses. -/
@[simp]
theorem erase_deduplicateByLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.erase =
      ⟨source.erase.clauses.dedup⟩ := by
  simp [deduplicateByLiterals, erase,
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
  constructor
  · intro satisfies translate clause clauseMember
    exact satisfies translate clause
      ((clause_mem_erase_deduplicateByLiterals_iff
        source clause).mpr clauseMember)
  · intro satisfies translate clause clauseMember
    exact satisfies translate clause
      ((clause_mem_erase_deduplicateByLiterals_iff
        source clause).mp clauseMember)

/-- Removing duplicate positioned protoclauses preserves periodic
satisfiability. -/
@[simp]
theorem deduplicateByLiterals_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.erase.Satisfiable ↔
      source.erase.Satisfiable := by
  unfold PeriodicCNF.Satisfiable
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨assignment,
        (source.deduplicateByLiterals_satisfies_iff assignment).mp
          satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨assignment,
        (source.deduplicateByLiterals_satisfies_iff assignment).mpr
          satisfies⟩

/-- Clause locality is insensitive to duplicate removal. -/
@[simp]
theorem deduplicateByLiterals_isLocal_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    source.deduplicateByLiterals.erase.IsLocal ↔
      source.erase.IsLocal := by
  unfold PeriodicCNF.IsLocal
  constructor
  · intro localProof clause clauseMember
    exact localProof clause
      ((clause_mem_erase_deduplicateByLiterals_iff
        source clause).mpr clauseMember)
  · intro localProof clause clauseMember
    exact localProof clause
      ((clause_mem_erase_deduplicateByLiterals_iff
        source clause).mp clauseMember)

/-- Every clause-width bound is insensitive to duplicate removal. -/
@[simp]
theorem deduplicateByLiterals_widthAtMost_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (width : Nat) :
    source.deduplicateByLiterals.erase.WidthAtMost width ↔
      source.erase.WidthAtMost width := by
  unfold PeriodicCNF.WidthAtMost
  constructor
  · intro bounded clause clauseMember
    exact bounded clause
      ((clause_mem_erase_deduplicateByLiterals_iff
        source clause).mpr clauseMember)
  · intro bounded clause clauseMember
    exact bounded clause
      ((clause_mem_erase_deduplicateByLiterals_iff
        source clause).mp clauseMember)

end PositionedPeriodicCNF
end LeanTrominoes
