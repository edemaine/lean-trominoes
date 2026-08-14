/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedIndex

/-! # Fresh-position irrelevance for positioned polarity metadata -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationPositioned

open PeriodicOneInThreePolarityNormalization

theorem complementClauseMetadataFrom_eq_of_complementClause
    {Variable : Type*} (first second : Positions Variable)
    (same : first.complementClause = second.complementClause)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    complementClauseMetadataFrom first sourceClause sourceClauseIndex
        literalStart source =
      complementClauseMetadataFrom second sourceClause sourceClauseIndex
        literalStart source := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart <;>
        simp [complementClauseMetadataFrom, compatible,
          positionedComplementClause, same, induction (literalStart + 1)]

theorem clauseMetadataFor_eq_of_complementClause
    {Variable : Type*} (first second : Positions Variable)
    (same : first.complementClause = second.complementClause)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    clauseMetadataFor first sourceClauseIndex sourceClause =
      clauseMetadataFor second sourceClauseIndex sourceClause := by
  simp [clauseMetadataFor,
    complementClauseMetadataFrom_eq_of_complementClause
      first second same]

theorem formulaClauseMetadata_eq_of_complementClause
    {Variable : Type*} (first second : Positions Variable)
    (same : first.complementClause = second.complementClause)
    (source : PositionedPeriodicCNF Variable) :
    formulaClauseMetadata first source =
      formulaClauseMetadata second source := by
  unfold formulaClauseMetadata
  apply congrArg (fun block => source.clauses.zipIdx.flatMap block)
  funext taggedSource
  exact clauseMetadataFor_eq_of_complementClause first second same
    taggedSource.2 taggedSource.1

end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
