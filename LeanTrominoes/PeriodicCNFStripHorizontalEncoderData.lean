/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripPlanarReduction

/-!
# Named inputs of the concrete routed padded encoder
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

local instance retainedTargetVariableDecidableEq : DecidableEq
    (OneInThreeNoUnitVariable
      (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
        Variable)) :=
  PeriodicOrthocrossing.retainedPolarityNormalizedVariableDecidableEq

/-- The final gauged positioned exact-one formula sent to routed polarity
normalization. -/
def horizontalFormula (source : PeriodicCNF Nat) :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
    (sourceFormula source)
    (sourceFormula_isLocal source)
    (sourceFormula_widthAtMostThree source)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
    (sourceFormula_clausesNonempty source)

/-- The matching final gauged variable placement. -/
def horizontalPlacement (source : PeriodicCNF Nat) :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
    (sourceFormula source)

/-- The matching clockwise ordered incidence routes. -/
def horizontalRoutes (source : PeriodicCNF Nat) :=
  (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
    (sourceFormula source)
    (sourceFormula_isLocal source)
    (sourceFormula_widthAtMostThree source)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
    (sourceFormula_clausesNonempty source)).routes

end PeriodicCNFStripReduction
end LeanTrominoes
