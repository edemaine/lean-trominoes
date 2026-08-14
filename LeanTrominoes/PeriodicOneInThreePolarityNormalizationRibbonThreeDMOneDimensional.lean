/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDM
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationFreshGaugeOneDimensional
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalizedOneDimensional

/-!
# One-dimensionality of the padded polarity-normalized 3DM target
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Routed polarity normalization followed by the padded planar 3DM encoder
preserves one-dimensionality. -/
theorem paddedPeriodicThreeDMProblem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (horizontal : source.erase.IsOneDimensional) :
    (paddedPeriodicThreeDMProblem
      source sourcePlacement sourceRoutes).IsOneDimensional := by
  unfold paddedPeriodicThreeDMProblem
  apply PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_isOneDimensional
  simpa only [PositionedPeriodicCNF.erase_scale] using
    formula_erase_isOneDimensional sourcePlacement sourceRoutes horizontal

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
