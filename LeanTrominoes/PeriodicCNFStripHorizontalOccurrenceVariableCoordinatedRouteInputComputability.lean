/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteSlotEncoding

/-! # Computability of variable coordinated-route table inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : Inhabited VariableSiteSlot := ⟨.first⟩

private theorem occurrenceVariableSiteSlot_primrec :
    Primrec occurrenceVariableSiteSlot :=
  Computability.finiteDomain_primrec _

theorem horizontalOccurrenceVariableCoordinatedRouteInputComputed_primrec :
    Primrec horizontalOccurrenceVariableCoordinatedRouteInputComputed := by
  exact Primrec.pair
    (horizontalOccurrenceVariableRibbonFanDataComputed_primrec.comp
      (Primrec.fst.comp Primrec.fst))
    (Primrec.pair
      (occurrenceVariableSiteSlot_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
