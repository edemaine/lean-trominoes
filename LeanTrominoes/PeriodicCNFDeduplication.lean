import LeanTrominoes.PeriodicCNF
import Mathlib.Data.List.Dedup

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

end PeriodicCNF
end LeanTrominoes
