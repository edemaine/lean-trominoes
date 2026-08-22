/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseNormalization

/-! # Pointwise normalized retained routed-variable clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Each named routed-variable implication is the matching generic
normalized-link clause after the complete retained periodic normalization
pipeline. -/
theorem normalizedClause_routedVariableClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (forward : Bool) :
    normalizedClause source
        (routedVariableClauseMetadataAt
          site armIndex arm link forward) =
      PeriodicEquality.normalizedClause
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source) link,
          forward) := by
  have pair := routedVariableLink_normalizedClauses_eq
    source site armIndex arm link
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
