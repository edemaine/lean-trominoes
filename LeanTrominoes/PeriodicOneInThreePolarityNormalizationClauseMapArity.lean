/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeAnchorNormalization
import LeanTrominoes.PeriodicOneInThreePolarityNormalization

/-! # Polarity-normalization arities under clause maps -/

namespace LeanTrominoes.PeriodicCNF

/-- Clause-anchor normalization preserves the clause-arity sequence of an
ordinary periodic CNF. -/
theorem anchorNormalize_clauseLengths
    {Variable : Type} (source : PeriodicCNF Variable) :
    source.anchorNormalize.clauses.map List.length =
      source.clauses.map List.length := by
  simp [PeriodicCNF.anchorNormalize,
    PeriodicClause.anchorNormalize_length]

end LeanTrominoes.PeriodicCNF

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalization

/-- Mapping literals without changing their polarity preserves the lengths
of all emitted complement clauses. -/
theorem complementClausesFrom_map_lengths_of_value
    {Source Target : Type}
    (transform : PeriodicLiteral Source → PeriodicLiteral Target)
    (valueEq : ∀ literal, (transform literal).value = literal.value)
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Source) :
    (complementClausesFrom clauseIndex literalStart
      (source.map transform)).map List.length =
      (complementClausesFrom clauseIndex literalStart source).map
        List.length := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      simp only [List.map_cons]
      rw [complementClausesFrom_cons, complementClausesFrom_cons,
        valueEq]
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [compatible, induction (literalStart + 1)]
      · simp [compatible, complementClause,
          induction (literalStart + 1)]

/-- A polarity-preserving literal map leaves one source clause's complete
normalized arity block unchanged. -/
theorem clauseClauses_map_lengths_of_value
    {Source Target : Type}
    (transform : PeriodicLiteral Source → PeriodicLiteral Target)
    (valueEq : ∀ literal, (transform literal).value = literal.value)
    (clauseIndex : Nat) (source : PeriodicClause Source) :
    (clauseClauses clauseIndex (source.map transform)).map List.length =
      (clauseClauses clauseIndex source).map List.length := by
  simp only [clauseClauses, List.map_cons, normalizeClause_length,
    List.length_map, complementClauses]
  exact congrArg (List.cons source.length)
    (complementClausesFrom_map_lengths_of_value
      transform valueEq clauseIndex 0 source)

/-- If a presentation map preserves each clause's normalized arity block,
then it preserves the complete formula output arity sequence. -/
theorem formula_mapClauses_clauseLengths
    {Source Target : Type}
    (source : PeriodicCNF Source)
    (transform : PeriodicClause Source → PeriodicClause Target)
    (blockEq : ∀ clauseIndex clause,
      (clauseClauses clauseIndex (transform clause)).map List.length =
        (clauseClauses clauseIndex clause).map List.length) :
    (formula ⟨source.clauses.map transform⟩).clauses.map List.length =
      (formula source).clauses.map List.length := by
  unfold formula
  rw [List.map_flatMap, List.map_flatMap]
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  exact blockEq clauseIndex clause

/-- Clause-anchor normalization changes offsets only, so applying polarity
normalization afterwards produces the same clause-arity sequence. -/
theorem formula_anchorNormalize_clauseLengths
    {Variable : Type} (source : PeriodicCNF Variable) :
    (formula source.anchorNormalize).clauses.map List.length =
      (formula source).clauses.map List.length := by
  apply formula_mapClauses_clauseLengths
  intro clauseIndex clause
  exact clauseClauses_map_lengths_of_value
    (fun literal => literal.anchorNormalize
      (PeriodicCNF.clauseAnchor clause))
    (fun literal => PeriodicLiteral.anchorNormalize_value
      (PeriodicCNF.clauseAnchor clause) literal)
    clauseIndex clause

end LeanTrominoes.PeriodicOneInThreePolarityNormalization
