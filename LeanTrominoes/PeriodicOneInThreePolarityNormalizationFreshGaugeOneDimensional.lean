/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationOneDimensional
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-!
# One-dimensional fresh-variable polarity gauge

The routed polarity layer gauges each fresh complement variable by the
negative of its retained source offset.  Fresh literal offsets therefore
become zero, while embedded originals retain their horizontal source offset.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

/-- Gauging one normalized occurrence makes its vertical offset zero when
the source occurrence is horizontal. -/
theorem normalizeLiteral_freshGauge_vertical_eq_zero
    {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (horizontal : source.offset.2 = 0) :
    ((normalizeLiteral clauseIndex literalIndex source).variableGauge
      freshGauge).offset.2 = 0 := by
  by_cases compatible :
      source.value = normalizedPolarity literalIndex
  · simpa [normalizeLiteral, compatible, liftLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add] using horizontal
  · rcases source with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
    simp [normalizeLiteral, compatible, complementLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add, Cell.sub]

/-- Gauging every normalized literal in a source suffix yields zero vertical
offsets. -/
theorem normalizeClauseFrom_freshGauge_isOneDimensional
    {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ literal ∈ normalizeClauseFrom clauseIndex literalStart source,
      (literal.variableGauge freshGauge).offset.2 = 0 := by
  intro literal literalMember
  simp only [normalizeClauseFrom, List.mem_map] at literalMember
  obtain ⟨tagged, taggedMember, rfl⟩ := literalMember
  exact normalizeLiteral_freshGauge_vertical_eq_zero
    clauseIndex tagged.2 tagged.1
    (horizontal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))

/-- Gauging either literal of a complement clause yields zero vertical
offset. -/
theorem complementClause_freshGauge_isOneDimensional
    {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (horizontal : source.offset.2 = 0) :
    ∀ literal ∈ complementClause clauseIndex literalIndex source,
      (literal.variableGauge freshGauge).offset.2 = 0 := by
  intro literal literalMember
  simp only [complementClause, List.mem_cons, List.not_mem_nil, or_false]
    at literalMember
  rcases literalMember with rfl | rfl
  · rcases source with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
    simp [complementFalseLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add, Cell.sub]
  · simpa [originalFalseLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add] using horizontal

/-- Every filtered complement clause remains horizontal after the fresh
gauge. -/
theorem complementClausesFrom_freshGauge_areOneDimensional
    {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ clause ∈ complementClausesFrom clauseIndex literalStart source,
      ∀ literal ∈ clause,
        (literal.variableGauge freshGauge).offset.2 = 0 := by
  intro clause clauseMember literal literalMember
  simp only [complementClausesFrom, List.mem_filterMap] at clauseMember
  obtain ⟨tagged, taggedMember, clauseEqual⟩ := clauseMember
  split at clauseEqual
  · contradiction
  · simp only [Option.some.injEq] at clauseEqual
    subst clause
    exact complementClause_freshGauge_isOneDimensional
      clauseIndex tagged.2 tagged.1
      (horizontal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))
      literal literalMember

/-- Every literal in one polarity-normalization block becomes horizontal
after the fresh gauge. -/
theorem clauseClauses_freshGauge_areOneDimensional
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ clause ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ clause,
        (literal.variableGauge freshGauge).offset.2 = 0 := by
  intro clause clauseMember literal literalMember
  simp only [clauseClauses, List.mem_cons] at clauseMember
  rcases clauseMember with rfl | clauseMember
  · exact normalizeClauseFrom_freshGauge_isOneDimensional
      clauseIndex 0 source horizontal literal literalMember
  · exact complementClausesFrom_freshGauge_areOneDimensional
      clauseIndex 0 source horizontal clause clauseMember
      literal literalMember

/-- Logical polarity normalization followed by the routed fresh-variable
gauge preserves one-dimensionality. -/
theorem formula_variableGauge_freshGauge_isOneDimensional
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    ((PeriodicOneInThreePolarityNormalization.formula source).variableGauge
      freshGauge).IsOneDimensional := by
  intro outputClause outputClauseMember outputLiteral outputLiteralMember
  simp only [PeriodicCNF.variableGauge, List.mem_map] at outputClauseMember
  obtain ⟨rawClause, rawClauseMember, rfl⟩ := outputClauseMember
  simp only [PeriodicClause.variableGauge, List.mem_map]
    at outputLiteralMember
  obtain ⟨rawLiteral, rawLiteralMember, rfl⟩ := outputLiteralMember
  simp only [PeriodicOneInThreePolarityNormalization.formula,
    List.mem_flatMap] at rawClauseMember
  obtain ⟨taggedClause, taggedClauseMember, rawClauseMember⟩ :=
    rawClauseMember
  exact clauseClauses_freshGauge_areOneDimensional
    taggedClause.2 taggedClause.1
    (horizontal taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    rawClause rawClauseMember rawLiteral rawLiteralMember

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
