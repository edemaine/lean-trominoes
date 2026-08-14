/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalGauge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOneDimensional

/-!
# One-dimensional normalized planar 3DM problem

The geometric planar reduction consumes a positioned source after erasing
positions and normalizing every clause anchor.  This wrapper connects that
normalization to the horizontal planar Figure 10 encoder.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- The exact natural-number 3DM problem used by the planar drawing is one
dimensional whenever its erased positioned source is one dimensional. -/
theorem normalizedProblem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (horizontal : source.erase.IsOneDimensional) :
    (normalizedProblem source placement).IsOneDimensional := by
  unfold normalizedProblem
  apply encodedProblem_isOneDimensional
  rw [normalizedSource_eq]
  exact PeriodicCNF.anchorNormalize_isOneDimensional horizontal

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
