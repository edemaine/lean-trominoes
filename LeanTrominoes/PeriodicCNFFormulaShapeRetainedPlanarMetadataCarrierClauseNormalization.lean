/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierVariableNormalizationData
import LeanTrominoes.PeriodicCNFPlanarSATClauseIndex
import LeanTrominoes.PeriodicEqualityNormalization

/-! # Normalized retained carrier clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Mapping one physical carrier equality through periodicization, wrapping,
the canonical variable gauge, and clause anchoring gives the generic pair of
normalized implication clauses for one normalized link. -/
theorem carrierLink_normalizedClauses_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    (drawingPlanarSATCarrierClauseMetadataFor
        (Variable := Variable) link).map
        (normalizedClause source) =
      (([PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source) link].product
        [true, false]).map PeriodicEquality.normalizedClause) := by
  rw [← PeriodicEquality.equalityInstance_normalized
    (carrierWrappedVariableNormalization source) link]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
