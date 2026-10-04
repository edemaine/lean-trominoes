/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCNFReplacementOffsets
import LeanTrominoes.FiniteCNFUniformOffsets
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationFreshGaugeOneDimensional

/-! # Routed polarity normalization preserves finite offsets -/
namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

/-- Gauging one normalized occurrence makes its offset zero when
the source occurrence is zero. -/
theorem normalizeLiteral_freshGauge_offset_eq_zero
    {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (zero : source.offset = (0,0)) :
    ((normalizeLiteral clauseIndex literalIndex source).variableGauge
      freshGauge).offset = (0,0) := by
  by_cases compatible :
      source.value = normalizedPolarity literalIndex
  · simpa [normalizeLiteral, compatible, liftLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add] using zero
  · rcases source with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
    simp [normalizeLiteral, compatible, complementLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add, Cell.sub]

/-- Gauging every normalized literal in a source suffix yields zero
offsets. -/
theorem normalizeClauseFrom_freshGauge_zeroOffsets
    {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (zero : ∀ literal ∈ source, literal.offset = (0,0)) :
    ∀ literal ∈ normalizeClauseFrom clauseIndex literalStart source,
      (literal.variableGauge freshGauge).offset = (0,0) := by
  intro literal literalMember
  simp only [normalizeClauseFrom, List.mem_map] at literalMember
  obtain ⟨tagged, taggedMember, rfl⟩ := literalMember
  exact normalizeLiteral_freshGauge_offset_eq_zero
    clauseIndex tagged.2 tagged.1
    (zero tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))

/-- Gauging either literal of a complement clause yields zero
offset. -/
theorem complementClause_freshGauge_zeroOffsets
    {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (zero : source.offset = (0,0)) :
    ∀ literal ∈ complementClause clauseIndex literalIndex source,
      (literal.variableGauge freshGauge).offset = (0,0) := by
  intro literal literalMember
  simp only [complementClause, List.mem_cons, List.not_mem_nil, or_false]
    at literalMember
  rcases literalMember with rfl | rfl
  · rcases source with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
    simp [complementFalseLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add, Cell.sub]
  · simpa [originalFalseLiteral, freshGauge,
      PeriodicLiteral.variableGauge, Cell.add] using zero

/-- Every filtered complement clause remains zero after the fresh
gauge. -/
theorem complementClausesFrom_freshGauge_zeroOffsets
    {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (zero : ∀ literal ∈ source, literal.offset = (0,0)) :
    ∀ clause ∈ complementClausesFrom clauseIndex literalStart source,
      ∀ literal ∈ clause,
        (literal.variableGauge freshGauge).offset = (0,0) := by
  intro clause clauseMember literal literalMember
  simp only [complementClausesFrom, List.mem_filterMap] at clauseMember
  obtain ⟨tagged, taggedMember, clauseEqual⟩ := clauseMember
  split at clauseEqual
  · contradiction
  · simp only [Option.some.injEq] at clauseEqual
    subst clause
    exact complementClause_freshGauge_zeroOffsets
      clauseIndex tagged.2 tagged.1
      (zero tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))
      literal literalMember

/-- Every literal in one polarity-normalization block becomes zero
after the fresh gauge. -/
theorem clauseClauses_freshGauge_zeroOffsets
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (zero : ∀ literal ∈ source, literal.offset = (0,0)) :
    ∀ clause ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ clause,
        (literal.variableGauge freshGauge).offset = (0,0) := by
  intro clause clauseMember literal literalMember
  simp only [clauseClauses, List.mem_cons] at clauseMember
  rcases clauseMember with rfl | clauseMember
  · exact normalizeClauseFrom_freshGauge_zeroOffsets
      clauseIndex 0 source zero literal literalMember
  · exact complementClausesFrom_freshGauge_zeroOffsets
      clauseIndex 0 source zero clause clauseMember
      literal literalMember

/-- Logical polarity normalization followed by the routed fresh-variable
gauge preserves zero offsets. -/
theorem formula_variableGauge_freshGauge_zeroOffsets
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets ((PeriodicOneInThreePolarityNormalization.formula source).variableGauge
      freshGauge) := by
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
  exact clauseClauses_freshGauge_zeroOffsets
    taggedClause.2 taggedClause.1
    (zero taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    rawClause rawClauseMember rawLiteral rawLiteralMember

/-- The erased routed polarity-normalization formula is finite
whenever the erased positioned source is finite. -/
theorem formula_erase_zeroOffsets
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (zero : FiniteCNF.ZeroOffsets source.erase) :
    FiniteCNF.ZeroOffsets (formula source sourcePlacement routes).erase := by
  rw [erase_formula]
  apply formula_variableGauge_freshGauge_zeroOffsets
  rw [refinedSource, PositionedPeriodicCNF.erase_scale,
    PositionedPeriodicCNF.erase_anchorNormalize]
  apply FiniteCNF.uniformOffsets_anchorNormalize
  intro clause member
  exact ⟨(0,0),zero clause member⟩

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
