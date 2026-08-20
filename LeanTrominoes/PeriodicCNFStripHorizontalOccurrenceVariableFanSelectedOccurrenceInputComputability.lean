/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSourceAtomComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSelectedSiteSlotComputability

/-! # Computability of selected variable-fan occurrence inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : Inhabited OccurrenceSlot := ⟨.first⟩

private theorem variableSiteOccurrenceSlot_primrec :
    Primrec variableSiteOccurrenceSlot :=
  Computability.finiteDomain_primrec _

theorem horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed_primrec :
    Primrec
      horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed := by
  exact Primrec.pair
    (horizontalOccurrenceVariableRibbonSourceAtom_primrec.comp Primrec.fst)
    (variableSiteOccurrenceSlot_primrec.comp
      horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed_primrec)

end PeriodicCNFStripReduction
end LeanTrominoes
