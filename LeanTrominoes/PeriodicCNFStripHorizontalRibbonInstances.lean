/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData
import LeanTrominoes.PeriodicCNFStripPlanarReduction
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonFans

/-! # Shared equality instances for the horizontal ribbon compiler -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

noncomputable section

attribute [local instance] variableDecidableEq

/-- Equality used by the final gauged finite-gadget presentation. -/
@[reducible] def horizontalRibbonInnerVariableDecidableEq :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
          Variable)) :=
  PeriodicOrthocrossing.finalGaugedRibbonFansVariableDecidableEq

@[reducible] local instance horizontalRibbonInnerVariableInstance :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
          Variable)) :=
  horizontalRibbonInnerVariableDecidableEq

/-- Equality for routed polarity-normalized variables, built from exactly the
same inner decision procedure as the semantic ribbon presentation. -/
@[reducible] def horizontalRibbonRoutedVariableDecidableEq :
    DecidableEq RoutedVariable :=
  fun first second =>
  @instDecidableEqSum
    (OneInThreeNoUnitVariable
      (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
        Variable))
    ((Nat × Nat) ×
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
            Variable)))
    PeriodicOrthocrossing.finalGaugedRibbonFansVariableDecidableEq
    (@instDecidableEqProd
      (Nat × Nat)
      (PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
            Variable)))
      (@instDecidableEqProd Nat Nat instDecidableEqNat instDecidableEqNat)
      (@instDecidableEqPeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
            Variable))
        PeriodicOrthocrossing.finalGaugedRibbonFansVariableDecidableEq))
    first second

end
end PeriodicCNFStripReduction
end LeanTrominoes
