/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PeriodicOneInThreePolarityNormalization
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-! # Polarity-normalization arities through variable gauges -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- A variable gauge preserves the clause-arity sequence of an ordinary
periodic CNF. -/
theorem variableGauge_clauseLengths
    {Variable : Type} (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    (source.variableGauge gauge).clauses.map List.length =
      source.clauses.map List.length := by
  simp [PeriodicCNF.variableGauge,
    PeriodicClause.variableGauge_length]

end PeriodicCNF

namespace PeriodicOneInThreePolarityNormalization

/-- A variable gauge changes offsets but neither the compatibility test nor
the lengths of complement clauses. -/
theorem complementClausesFrom_variableGauge_lengths
    {Variable : Type} (gauge : Variable → Cell)
    (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (complementClausesFrom clauseIndex literalStart
      (source.variableGauge gauge)).map List.length =
      (complementClausesFrom clauseIndex literalStart source).map
        List.length := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      simp only [PeriodicClause.variableGauge, List.map_cons]
      rw [complementClausesFrom_cons, complementClausesFrom_cons]
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [compatible]
        simpa only [PeriodicClause.variableGauge] using
          induction (literalStart + 1)
      · simp [compatible, complementClause]
        simpa only [PeriodicClause.variableGauge] using
          induction (literalStart + 1)

/-- One gauged source clause emits the same polarity-normalized arity block
as the ungauged clause. -/
theorem clauseClauses_variableGauge_lengths
    {Variable : Type} (gauge : Variable → Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    (clauseClauses clauseIndex
      (source.variableGauge gauge)).map List.length =
      (clauseClauses clauseIndex source).map List.length := by
  simp only [clauseClauses, List.map_cons,
    normalizeClause_length, PeriodicClause.variableGauge_length,
    complementClauses]
  exact congrArg (List.cons source.length)
    (complementClausesFrom_variableGauge_lengths
      gauge clauseIndex 0 source)

/-- Applying polarity normalization after a whole-formula variable gauge
preserves the complete clause-arity sequence. -/
theorem formula_variableGauge_clauseLengths
    {Variable : Type} (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    (formula (source.variableGauge gauge)).clauses.map List.length =
      (formula source).clauses.map List.length := by
  unfold formula PeriodicCNF.variableGauge
  rw [List.map_flatMap, List.map_flatMap]
  change
    List.flatMap
        (fun tagged =>
          (clauseClauses tagged.2 tagged.1).map List.length)
        ((source.clauses.map
          (PeriodicClause.variableGauge gauge)).zipIdx) =
      List.flatMap
        (fun tagged =>
          (clauseClauses tagged.2 tagged.1).map List.length)
        source.clauses.zipIdx
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  exact clauseClauses_variableGauge_lengths
    gauge clauseIndex clause

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
