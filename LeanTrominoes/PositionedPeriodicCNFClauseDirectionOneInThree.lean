import LeanTrominoes.PeriodicOneInThree
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-!
# Exact-one semantics under clause-direction ordering

Clockwise clause ordering changes only the order of literal occurrences in
each clause.  The general ordering module records ordinary CNF semantics;
this file supplies the analogous invariant for exact-one semantics.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

variable {Variable : Type*}

/-- Permuting a periodic clause does not change its exact-one truth value. -/
theorem periodicOneInThree_clauseHolds_iff_of_perm
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    {first second : PeriodicClause Variable}
    (permutation : first.Perm second) :
    PeriodicOneInThree.ClauseHolds assignment translate first ↔
      PeriodicOneInThree.ClauseHolds assignment translate second := by
  unfold PeriodicOneInThree.ClauseHolds
    PeriodicOneInThree.ExactlyOne PeriodicOneInThree.clauseValues
  rw [List.Perm.count_eq
    (permutation.map fun literal =>
      assignment literal.atom (Cell.add translate literal.offset) ==
        literal.value) true]

/-- Clockwise clause ordering preserves exact-one satisfaction by a fixed
plane-wide assignment. -/
theorem orderClausesByRouteDirection_oneInThreeSatisfies_iff
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (assignment : Variable → Cell → Bool) :
    PeriodicOneInThree.Satisfies
        (orderClausesByRouteDirection source routes).erase assignment ↔
      PeriodicOneInThree.Satisfies source.erase assignment := by
  constructor
  · intro satisfies translate clause clauseMember
    change clause ∈
      source.clauses.map PositionedPeriodicClause.literals at clauseMember
    rcases List.mem_map.mp clauseMember with
      ⟨sourceClause, sourceClauseMember, rfl⟩
    have indexedMember :
        sourceClause ∈ source.clauses.zipIdx.map Prod.fst := by
      simpa only [List.zipIdx_map_fst] using sourceClauseMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEq⟩
    have orderedMember :=
      orderClauseByRouteDirection_mem routes taggedClauseMember
    have erasedOrderedMember :
        (orderClauseByRouteDirection
          routes taggedClause.2 taggedClause.1).literals ∈
          (orderClausesByRouteDirection source routes).erase.clauses := by
      change _ ∈
        (orderClausesByRouteDirection source routes).clauses.map
          PositionedPeriodicClause.literals
      exact List.mem_map.mpr
        ⟨_, List.fst_mem_of_mem_zipIdx orderedMember, rfl⟩
    have orderedHolds := satisfies translate _ erasedOrderedMember
    subst sourceClause
    exact
      (periodicOneInThree_clauseHolds_iff_of_perm assignment translate
        (orderClauseByRouteDirection_literals_perm
          routes taggedClause.2 taggedClause.1)).mp orderedHolds
  · intro satisfies translate clause clauseMember
    change clause ∈
      (orderClausesByRouteDirection source routes).clauses.map
        PositionedPeriodicClause.literals at clauseMember
    rcases List.mem_map.mp clauseMember with
      ⟨orderedClause, orderedClauseMember, rfl⟩
    have indexedMember :
        orderedClause ∈
          (orderClausesByRouteDirection source routes).clauses.zipIdx.map
            Prod.fst := by
      simpa only [List.zipIdx_map_fst] using orderedClauseMember
    rcases List.mem_map.mp indexedMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEq⟩
    rcases exists_sourceClause_of_orderedClause_mem
        routes taggedClauseMember with
      ⟨sourceClause, sourceClauseMember, sourceClauseEq⟩
    have sourceHolds :
        PeriodicOneInThree.ClauseHolds
          assignment translate sourceClause.literals :=
      satisfies translate sourceClause.literals
        (by
          change sourceClause.literals ∈
            source.clauses.map PositionedPeriodicClause.literals
          exact List.mem_map.mpr
            ⟨sourceClause,
              List.fst_mem_of_mem_zipIdx sourceClauseMember, rfl⟩)
    subst orderedClause
    rw [sourceClauseEq]
    exact
      (periodicOneInThree_clauseHolds_iff_of_perm assignment translate
        (orderClauseByRouteDirection_literals_perm
          routes taggedClause.2 sourceClause)).mpr sourceHolds

/-- Clockwise clause ordering preserves exact-one satisfiability exactly. -/
theorem orderClausesByRouteDirection_oneInThreeSatisfiable_iff
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    PeriodicOneInThree.Satisfiable
        (orderClausesByRouteDirection source routes).erase ↔
      PeriodicOneInThree.Satisfiable source.erase := by
  constructor <;> rintro ⟨assignment, satisfies⟩
  · exact ⟨assignment,
      (orderClausesByRouteDirection_oneInThreeSatisfies_iff
        source routes assignment).mp satisfies⟩
  · exact ⟨assignment,
      (orderClausesByRouteDirection_oneInThreeSatisfies_iff
        source routes assignment).mpr satisfies⟩

end PositionedPeriodicCNF
end LeanTrominoes
