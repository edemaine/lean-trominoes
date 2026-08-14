/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-!
# One-dimensionality through strip-source normalization

Width-three auxiliary literals inherit the source clause's anchor, while
occurrence copies inherit their source literal offset and implication-cycle
literals use offset zero.  Consequently the complete guarded 3SAT-3 source
for the strip reduction remains one dimensional.
-/

namespace LeanTrominoes

namespace PeriodicThreeCNF

/-- Every generated literal supported by a horizontal source clause remains
horizontal. -/
theorem Supported.vertical_eq_zero
    {Variable : Type*}
    {source : PeriodicClause Variable}
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0)
    {literal : PeriodicLiteral (ThreeCNFVariable Variable)}
    (supported : Supported source literal) :
    literal.offset.2 = 0 := by
  rcases supported with
    ⟨original, originalMember, rfl⟩ |
      ⟨suffix, value, rfl⟩
  · simpa [liftLiteral] using horizontal original originalMember
  · cases source with
    | nil => rfl
    | cons first rest =>
        simpa [auxiliary, anchor] using
          horizontal first (by simp)

/-- Width-three conversion preserves the one-dimensional fragment. -/
theorem formula_isOneDimensional
    {Variable : Type*} {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (formula source).IsOneDimensional := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨sourceClause, sourceClauseMember, clauseMember⟩ := clauseMember
  exact Supported.vertical_eq_zero
    (horizontal sourceClause sourceClauseMember)
    (clauseClauses_supported sourceClause clause clauseMember
      literal literalMember)

end PeriodicThreeCNF

namespace PeriodicThreeSATThree

/-- Every implication-cycle clause is horizontal. -/
theorem implicationClause_isOneDimensional
    {Variable : Type*}
    (first second : ThreeOccurrenceVariable Variable) :
    ∀ literal ∈ implicationClause first second,
      literal.offset.2 = 0 := by
  simp [implicationClause]

theorem cycleFrom_isOneDimensional
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleFrom first current rest,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  induction rest generalizing current with
  | nil =>
      simpa [cycleFrom] using
        implicationClause_isOneDimensional current first
  | cons next rest induction =>
      intro clause clauseMember literal literalMember
      simp only [cycleFrom, List.mem_cons] at clauseMember
      rcases clauseMember with rfl | clauseMember
      · exact implicationClause_isOneDimensional current next
          literal literalMember
      · exact induction next clause clauseMember literal literalMember

theorem cycleClauses_isOneDimensional
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleClauses copies,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  cases copies with
  | nil => simp [cycleClauses]
  | cons first rest =>
      exact cycleFrom_isOneDimensional first first rest

theorem allCycleClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ∀ clause ∈ allCycleClauses source,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  intro clause clauseMember literal literalMember
  simp only [allCycleClauses, List.mem_flatMap] at clauseMember
  obtain ⟨atom, -, clauseMember⟩ := clauseMember
  exact cycleClauses_isOneDimensional
    (occurrenceVariables source atom)
    clause clauseMember literal literalMember

/-- An occurrence-copy clause inherits horizontal offsets pointwise. -/
theorem occurrenceClause_isOneDimensional
    {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ literal ∈ occurrenceClause clauseIndex source,
      literal.offset.2 = 0 := by
  intro literal literalMember
  simp only [occurrenceClause, List.mem_map] at literalMember
  obtain ⟨tagged, taggedMember, rfl⟩ := literalMember
  simpa [occurrenceLiteral] using
    horizontal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)

/-- Occurrence splitting preserves the one-dimensional fragment. -/
theorem formula_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (formula source).IsOneDimensional := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at occurrenceMember
    obtain ⟨taggedClause, taggedClauseMember, rfl⟩ := occurrenceMember
    exact occurrenceClause_isOneDimensional taggedClause.2 taggedClause.1
      (horizontal taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember))
      literal literalMember
  · exact allCycleClauses_isOneDimensional source
      clause cycleMember literal literalMember

end PeriodicThreeSATThree

namespace PeriodicCNFStripReduction

theorem fallbackFormula_isOneDimensional :
    fallbackFormula.IsOneDimensional := by
  simp [fallbackFormula, PeriodicCNF.IsOneDimensional]

theorem normalizedFormula_isOneDimensional
    (source : PeriodicCNF Nat) (horizontal : source.IsOneDimensional) :
    (normalizedFormula source).IsOneDimensional :=
  PeriodicThreeSATThree.formula_isOneDimensional
    (PeriodicThreeCNF.formula_isOneDimensional horizontal)

/-- The guarded planar source is horizontal even on malformed input. -/
theorem sourceFormula_isOneDimensional (source : PeriodicCNF Nat) :
    (sourceFormula source).IsOneDimensional := by
  by_cases admissible : SourceAdmissible source
  · simpa [sourceFormula, admissible] using
      normalizedFormula_isOneDimensional source admissible.1
  · simpa [sourceFormula, admissible] using
      fallbackFormula_isOneDimensional

end PeriodicCNFStripReduction
end LeanTrominoes
