/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned
import LeanTrominoes.PeriodicCNFOneDimensional

/-!
# Selecting indexed occurrences in a positioned periodic CNF
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Membership in the erased finite occurrence list selects a positioned
clause and literal at explicit presentation indices. -/
theorem exists_indexedOccurrence_of_mem_variableOccurrences
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {atom : Variable}
    (atomMember : atom ∈ source.erase.variableOccurrences) :
    ∃ clause clauseIndex literal literalIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx ∧
        (literal, literalIndex) ∈ clause.literals.zipIdx ∧
        literal.atom = atom := by
  unfold PeriodicCNF.variableOccurrences at atomMember
  rcases List.mem_flatMap.mp atomMember with
    ⟨literals, literalsMember, atomInLiterals⟩
  rcases List.mem_map.mp literalsMember with
    ⟨clause, clauseMember, rfl⟩
  rcases List.mem_map.mp atomInLiterals with
    ⟨literal, literalMember, literalAtomEq⟩
  rcases List.mem_iff_getElem.mp clauseMember with
    ⟨clauseIndex, clauseIndexLt, clauseAt⟩
  rcases List.mem_iff_getElem.mp literalMember with
    ⟨literalIndex, literalIndexLt, literalAt⟩
  refine ⟨clause, clauseIndex, literal, literalIndex, ?_, ?_,
    literalAtomEq⟩
  · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨clauseIndexLt, clauseAt⟩
  · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨literalIndexLt, literalAt⟩

/-- In a one-dimensional positioned formula, the selected indexed
occurrence additionally has vertical offset zero. -/
theorem exists_indexedHorizontalOccurrence_of_mem_variableOccurrences
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (horizontal : source.erase.IsOneDimensional)
    {atom : Variable}
    (atomMember : atom ∈ source.erase.variableOccurrences) :
    ∃ clause clauseIndex literal literalIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx ∧
        (literal, literalIndex) ∈ clause.literals.zipIdx ∧
        literal.atom = atom ∧
        literal.offset.2 = 0 := by
  rcases exists_indexedOccurrence_of_mem_variableOccurrences
      source atomMember with
    ⟨clause, clauseIndex, literal, literalIndex,
      clauseMember, literalMember, literalAtomEq⟩
  refine ⟨clause, clauseIndex, literal, literalIndex,
    clauseMember, literalMember, literalAtomEq, ?_⟩
  exact horizontal clause.literals
    (by
      change clause.literals ∈
        source.clauses.map PositionedPeriodicClause.literals
      exact List.mem_map.mpr
        ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩)
    literal (List.fst_mem_of_mem_zipIdx literalMember)

end PositionedPeriodicCNF
end LeanTrominoes
