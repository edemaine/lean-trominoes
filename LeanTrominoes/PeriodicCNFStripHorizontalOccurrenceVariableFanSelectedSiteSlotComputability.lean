/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanCountSecondComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanCountThirdComputability

/-! # Computability of variable-fan source-slot selection -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : Inhabited VariableSiteSlot := ⟨.first⟩

private theorem horizontalOccurrenceVariableRibbonSiteSlotSelect_primrec :
    Primrec horizontalOccurrenceVariableRibbonSiteSlotSelect :=
  Computability.finiteDomain_primrec _

theorem horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed := by
  exact horizontalOccurrenceVariableRibbonSiteSlotSelect_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (horizontalOccurrenceVariableRibbonCountSecondBoolComputed_primrec.comp
          Primrec.fst)
        (horizontalOccurrenceVariableRibbonCountThirdBoolComputed_primrec.comp
          Primrec.fst))
      Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
