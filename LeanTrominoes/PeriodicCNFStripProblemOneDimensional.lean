/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalProblemBridge
import LeanTrominoes.PeriodicCNFStripHorizontalFormula
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDMOneDimensional

/-!
# One-dimensional final 3DM problem for the strip reduction
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- The final polarity-normalized planar 3DM instance remains horizontal. -/
theorem problem_isOneDimensional (source : PeriodicCNF Nat) :
    (problem source).IsOneDimensional := by
  rw [← horizontalProblem_eq_problem source]
  unfold horizontalProblem
  exact
    @PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_isOneDimensional
      (OneInThreeNoUnitVariable
        (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
          Variable))
      (@PeriodicOrthocrossing.retainedPolarityNormalizedVariableDecidableEq
        Variable sourceVariableDecidableEq)
      (horizontalFormula source) (horizontalPlacement source)
      (horizontalRoutes source) (horizontalFormula_isOneDimensional source)

end PeriodicCNFStripReduction
end LeanTrominoes
