/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanCountSecondComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanCountThirdComputability

/-! # Computability of the horizontal variable-fan count code -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonCountPredComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonCountPredComputed := by
  exact Primrec.ite
    horizontalOccurrenceVariableRibbonCountSecondComputed_primrec
    (Primrec.ite
      horizontalOccurrenceVariableRibbonCountThirdComputed_primrec
      (Primrec.const (2 : Fin 3))
      (Primrec.const (1 : Fin 3)))
    (Primrec.const (0 : Fin 3))

end PeriodicCNFStripReduction
end LeanTrominoes
