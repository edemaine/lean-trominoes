/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-!
# One-dimensional positioned clause ordering

Ordering clause literals by route-exit direction changes neither the literal
values nor their periodic offsets.  Each ordered literal list is a
permutation of its source list.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Stable route-direction ordering preserves one-dimensionality after
positions are erased. -/
theorem orderClausesByRouteDirection_erase_isOneDimensional
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (horizontal : source.erase.IsOneDimensional) :
    (orderClausesByRouteDirection source routes).erase.IsOneDimensional := by
  intro outputClause outputClauseMember outputLiteral outputLiteralMember
  rw [PositionedPeriodicCNF.erase] at outputClauseMember
  rcases List.mem_map.mp outputClauseMember with
    ⟨outputPositionedClause, outputPositionedClauseMember, rfl⟩
  rw [orderClausesByRouteDirection] at outputPositionedClauseMember
  rcases List.mem_map.mp outputPositionedClauseMember with
    ⟨taggedSourceClause, taggedSourceClauseMember, rfl⟩
  have sourceClauseMember :
      taggedSourceClause.1.literals ∈ source.erase.clauses := by
    change taggedSourceClause.1.literals ∈
      source.clauses.map PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨taggedSourceClause.1,
        List.fst_mem_of_mem_zipIdx taggedSourceClauseMember, rfl⟩
  have sourceLiteralMember :
      outputLiteral ∈ taggedSourceClause.1.literals :=
    (orderClauseByRouteDirection_literals_perm
      routes taggedSourceClause.2 taggedSourceClause.1).mem_iff.mp
        outputLiteralMember
  exact horizontal taggedSourceClause.1.literals sourceClauseMember
    outputLiteral sourceLiteralMember

end PositionedPeriodicCNF
end LeanTrominoes
