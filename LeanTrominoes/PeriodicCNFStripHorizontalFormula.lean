/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData
import LeanTrominoes.PeriodicCNFStripOneDimensional
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGauge

/-!
# Horizontality of the final exact-one formula
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

local instance retainedTargetFormulaVariableDecidableEq : DecidableEq
    (OneInThreeNoUnitVariable
      (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
        Variable)) :=
  PeriodicOrthocrossing.retainedPolarityNormalizedVariableDecidableEq

/-- The final gauged exact-one formula remains one dimensional. -/
theorem horizontalFormula_isOneDimensional (source : PeriodicCNF Nat) :
    (horizontalFormula source).erase.IsOneDimensional := by
  unfold horizontalFormula
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_erase_isOneDimensional
      (PeriodicCNF.incidenceGraph_isWellFormed (sourceFormula source))
      (PeriodicCNF.incidenceGraph_degreeAtMost
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree source))
      (PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal source))
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)
      (PeriodicCNF.incidenceGraph_hasZeroVerticalOffsets
        (sourceFormula_isOneDimensional source))

end PeriodicCNFStripReduction
end LeanTrominoes
