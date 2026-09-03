/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteOperationSemantics

/-! # Flattened semantic polarity-metadata operation lists -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicCNF.ClauseProfilePolarityRouteOperation

/-- After forgetting global source-clause indices, the complete metadata
operation stream is the clause-major literal-value schedule. -/
theorem formulaClauseMetadata_flatMap_metadataIndexedDescriptorBlock_eq_values
    {Variable : Type}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        positions source).flatMap metadataIndexedDescriptorBlock =
      source.clauses.flatMap fun clause =>
        indexedDescriptors
          (clause.literals.map PeriodicLiteral.value) := by
  exact
    (formulaClauseMetadata_flatMap_metadataIndexedDescriptorBlock
      positions source).trans
      (PeriodicCNF.zipIdx_flatMap_fst
        (fun clause => indexedDescriptors
          (clause.literals.map PeriodicLiteral.value))
        source.clauses 0)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
