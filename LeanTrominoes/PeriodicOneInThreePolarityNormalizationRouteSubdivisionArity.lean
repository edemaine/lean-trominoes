/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationClauseMapArity
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationVariableGaugeArity

/-! # Clause arities through routed polarity normalization -/

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Anchor normalization, uniform refinement, positioned polarity
normalization, and the final fresh-variable gauge all preserve the complete
logical polarity-normalization clause-arity sequence. -/
theorem formula_clauseLengths
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (formula source sourcePlacement routes).erase.clauses.map List.length =
      (PeriodicOneInThreePolarityNormalization.formula
        source.erase).clauses.map List.length := by
  rw [erase_formula,
    PeriodicCNF.variableGauge_clauseLengths]
  simp only [refinedSource,
    PositionedPeriodicCNF.erase_scale,
    PositionedPeriodicCNF.erase_anchorNormalize]
  exact
    PeriodicOneInThreePolarityNormalization.formula_anchorNormalize_clauseLengths
      source.erase

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
