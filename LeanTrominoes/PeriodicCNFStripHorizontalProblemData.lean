/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData

/-!
# A direct horizontal view of the concrete strip problem

The direct name exposes the routed padded encoder at the head of the term,
so its one-dimensionality theorem elaborates without unfolding the complete
retained reduction alias.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- The final strip problem, expressed directly through the routed padded
3DM encoder. -/
def horizontalProblem (source : PeriodicCNF Nat) : PeriodicThreeDM :=
  letI : DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
          Variable)) :=
    PeriodicOrthocrossing.retainedPolarityNormalizedVariableDecidableEq
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem
    (horizontalFormula source) (horizontalPlacement source)
      (horizontalRoutes source)

end PeriodicCNFStripReduction
end LeanTrominoes
