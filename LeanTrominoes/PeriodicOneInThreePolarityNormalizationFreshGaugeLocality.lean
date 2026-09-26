/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.PeriodicCNFAnchorNormalizationLocality

/-! # Locality after the fresh-variable gauge of routed polarity normalization -/
namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
open PeriodicOneInThreePolarityNormalization

private def Supported {V : Type*} (source : PeriodicClause V)
    (literal : PeriodicLiteral (PolarityNormalizedVariable V)) : Prop :=
  (literal.variableGauge freshGauge).offset = (0,0) ∨
    ∃ original ∈ source, (literal.variableGauge freshGauge).offset = original.offset

private theorem normalized_supported {V : Type*} (ci li : Nat) (source : PeriodicClause V)
    (literal : PeriodicLiteral V) (member : literal ∈ source) :
    Supported source (normalizeLiteral ci li literal) := by
  by_cases compatible : literal.value = normalizedPolarity li
  · right
    exact ⟨literal, member, by simp [normalizeLiteral, compatible, liftLiteral,
      PeriodicLiteral.variableGauge, freshGauge, Cell.add]⟩
  · left
    rcases literal with ⟨a, ⟨x,y⟩, b⟩
    simp [normalizeLiteral, compatible, complementLiteral, PeriodicLiteral.variableGauge, freshGauge, Cell.add, Cell.sub]

private theorem complement_supported {V : Type*} (ci li : Nat) (source : PeriodicClause V)
    (original : PeriodicLiteral V) (member : original ∈ source)
    (literal : PeriodicLiteral (PolarityNormalizedVariable V))
    (belongs : literal ∈ complementClause ci li original) : Supported source literal := by
  simp only [complementClause, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl | rfl
  · left
    rcases original with ⟨a, ⟨x,y⟩, b⟩
    simp [complementFalseLiteral, PeriodicLiteral.variableGauge, freshGauge, Cell.add, Cell.sub]
  · right
    exact ⟨original, member, by simp [originalFalseLiteral, PeriodicLiteral.variableGauge, freshGauge, Cell.add]⟩

private theorem block_supported {V : Type*} (ci : Nat) (source : PeriodicClause V)
    (clause : PeriodicClause (PolarityNormalizedVariable V)) (hc : clause ∈ clauseClauses ci source)
    (literal : PeriodicLiteral (PolarityNormalizedVariable V)) (hl : literal ∈ clause) : Supported source literal := by
  simp only [clauseClauses, List.mem_cons] at hc
  rcases hc with rfl | hc
  · obtain ⟨tag, ht, rfl⟩ := List.mem_map.mp hl
    exact normalized_supported ci tag.2 source tag.1 (List.fst_mem_of_mem_zipIdx ht)
  · simp only [complementClauses, complementClausesFrom, List.mem_filterMap] at hc
    obtain ⟨tag, ht, he⟩ := hc
    split at he
    · contradiction
    · simp only [Option.some.injEq] at he
      subst clause
      exact complement_supported ci tag.2 source tag.1 (List.fst_mem_of_mem_zipIdx ht) literal hl

private theorem block_local {V : Type*} (ci : Nat) (source : PeriodicClause V)
    (locality : source.IsLocal) (zero : ∃ literal ∈ source, literal.offset = (0,0))
    (clause : PeriodicClause (PolarityNormalizedVariable V)) (hc : clause ∈ clauseClauses ci source) :
    (clause.variableGauge freshGauge).IsLocal := by
  have support (literal : PeriodicLiteral (PolarityNormalizedVariable V)) (hl : literal ∈ clause) :
      ∃ original ∈ source, (literal.variableGauge freshGauge).offset = original.offset := by
    rcases block_supported ci source clause hc literal hl with hz | hs
    · obtain ⟨original, ho, he⟩ := zero
      exact ⟨original, ho, hz.trans he.symm⟩
    · exact hs
  intro a ha b hb
  obtain ⟨first, hf, rfl⟩ := List.mem_map.mp ha
  obtain ⟨second, hs, rfl⟩ := List.mem_map.mp hb
  obtain ⟨originalFirst, hfirst, efirst⟩ := support first hf
  obtain ⟨originalSecond, hsecond, esecond⟩ := support second hs
  simpa only [PeriodicClause.offsetDistance, efirst, esecond] using locality originalFirst hfirst originalSecond hsecond

private theorem gauged_formula_local {V : Type*} (source : PeriodicCNF V)
    (locality : source.IsLocal)
    (zero : ∀ clause ∈ source.clauses, ∃ literal ∈ clause, literal.offset = (0,0)) :
    ((PeriodicOneInThreePolarityNormalization.formula source).variableGauge freshGauge).IsLocal := by
  intro clause member
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
  obtain ⟨tag, ht, hc⟩ := List.mem_flatMap.mp ho
  exact block_local tag.2 tag.1 (locality _ (List.fst_mem_of_mem_zipIdx ht))
    (zero _ (List.fst_mem_of_mem_zipIdx ht)) original hc

/-- Every normalized source clause has a zero-offset first literal. -/
private theorem normalized_zero {V : Type*} (source : PeriodicCNF V)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (clause : PeriodicClause V) (member : clause ∈ source.anchorNormalize.clauses) :
    ∃ literal ∈ clause, literal.offset = (0,0) := by
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
  cases original with
  | nil => exact (nonempty [] ho rfl).elim
  | cons first rest =>
      refine ⟨first.anchorNormalize first.offset, ?_, ?_⟩
      · simp [PeriodicClause.anchorNormalize, PeriodicCNF.clauseAnchor]
      · simp [PeriodicLiteral.anchorNormalize, Cell.sub]

/-- Routing and its fresh gauge preserve locality of nonempty source clauses. -/
theorem formula_erase_isLocal {V : Type*} (source : PositionedPeriodicCNF V)
    (placement : PeriodicVariablePlacement V) (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (locality : source.erase.IsLocal)
    (nonempty : ∀ clause ∈ source.erase.clauses, clause ≠ []) :
    (formula source placement routes).erase.IsLocal := by
  rw [erase_formula, refinedSource, PositionedPeriodicCNF.erase_scale, PositionedPeriodicCNF.erase_anchorNormalize]
  exact gauged_formula_local source.erase.anchorNormalize (PeriodicCNF.anchorNormalize_local locality)
    (normalized_zero source.erase nonempty)

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
