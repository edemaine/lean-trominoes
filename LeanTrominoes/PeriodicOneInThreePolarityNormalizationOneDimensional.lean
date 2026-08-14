/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicOneInThreePolarityNormalization

/-!
# One-dimensional exact-one polarity normalization

Every normalized occurrence and both literals of its optional complement
clause retain the source occurrence's periodic offset.  Thus logical polarity
normalization preserves the one-dimensional fragment.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization

/-- Normalizing a clause suffix preserves zero vertical offsets. -/
theorem normalizeClauseFrom_isOneDimensional
    {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ literal ∈ normalizeClauseFrom clauseIndex literalStart source,
      literal.offset.2 = 0 := by
  intro literal literalMember
  simp only [normalizeClauseFrom, List.mem_map] at literalMember
  obtain ⟨tagged, taggedMember, rfl⟩ := literalMember
  simpa using
    horizontal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)

/-- Both literals of a generated complement clause retain their source
occurrence's zero vertical offset. -/
theorem complementClause_isOneDimensional
    {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (horizontal : source.offset.2 = 0) :
    ∀ literal ∈ complementClause clauseIndex literalIndex source,
      literal.offset.2 = 0 := by
  intro literal literalMember
  simp only [complementClause, List.mem_cons, List.not_mem_nil, or_false]
    at literalMember
  rcases literalMember with rfl | rfl <;>
    simpa [complementFalseLiteral, originalFalseLiteral] using horizontal

/-- Every filtered complement clause emitted from a horizontal source suffix
has zero vertical offsets. -/
theorem complementClausesFrom_areOneDimensional
    {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ clause ∈ complementClausesFrom clauseIndex literalStart source,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  intro clause clauseMember literal literalMember
  simp only [complementClausesFrom, List.mem_filterMap] at clauseMember
  obtain ⟨tagged, taggedMember, clauseEqual⟩ := clauseMember
  split at clauseEqual
  · contradiction
  · simp only [Option.some.injEq] at clauseEqual
    subst clause
    exact complementClause_isOneDimensional clauseIndex tagged.2 tagged.1
      (horizontal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))
      literal literalMember

/-- Every clause in one polarity-normalization block is horizontal when its
source clause is horizontal. -/
theorem clauseClauses_areOneDimensional
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ clause ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  intro clause clauseMember literal literalMember
  simp only [clauseClauses, List.mem_cons] at clauseMember
  rcases clauseMember with rfl | clauseMember
  · exact normalizeClauseFrom_isOneDimensional clauseIndex 0 source
      horizontal literal literalMember
  · exact complementClausesFrom_areOneDimensional clauseIndex 0 source
      horizontal clause clauseMember literal literalMember

/-- Logical polarity normalization preserves one-dimensionality. -/
theorem formula_isOneDimensional
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (formula source).IsOneDimensional := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨taggedClause, taggedClauseMember, clauseMember⟩ := clauseMember
  exact clauseClauses_areOneDimensional taggedClause.2 taggedClause.1
    (horizontal taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    clause clauseMember literal literalMember

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
