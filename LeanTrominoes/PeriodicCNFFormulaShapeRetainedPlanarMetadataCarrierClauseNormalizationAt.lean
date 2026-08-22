/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseNormalization

/-! # Pointwise normalized retained carrier clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Each named carrier implication is the matching generic normalized-link
clause after the complete retained periodic normalization pipeline. -/
theorem normalizedClause_carrierClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (forward : Bool) :
    normalizedClause source (carrierClauseMetadataAt link forward) =
      PeriodicEquality.normalizedClause
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source) link,
          forward) := by
  have pair := carrierLink_normalizedClauses_eq source link
  cases forward with
  | false =>
      have second := congrArg
        (fun clauses => (clauses.drop 1).head?) pair
      simpa [List.product] using second
  | true =>
      have first := congrArg List.head? pair
      simpa [List.product] using first

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
