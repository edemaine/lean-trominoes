/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendClauseData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseNormalizationAt

/-! # Pointwise normalized retained bend clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A bend implication has the same normalized equality-link clause as its
underlying carrier link. -/
theorem normalizedClause_bendClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (forward : Bool) :
    normalizedClause source
        (bendClauseMetadataAt source.incidenceGraph routeBend forward) =
      PeriodicEquality.normalizedClause
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source)
          (routeBend.equalityLink source.incidenceGraph),
          forward) := by
  change normalizedClause source
      (carrierClauseMetadataAt
        (routeBend.equalityLink source.incidenceGraph) forward) = _
  exact normalizedClause_carrierClauseMetadataAt_eq source
    (routeBend.equalityLink source.incidenceGraph) forward

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
