/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSourceComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteSlotEncoding

/-! # Computability of finite variable-fan slot inputs -/

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

theorem horizontalOccurrenceVariableRibbonRouteInput_primrec :
    Primrec horizontalOccurrenceVariableRibbonRouteInput := by
  exact Primrec.pair Primrec.fst
    (variableSiteOccurrenceSlot_primrec.comp Primrec.snd)

theorem horizontalOccurrenceVariableRibbonLookupInput_primrec :
    Primrec horizontalOccurrenceVariableRibbonLookupInput := by
  exact Primrec.pair
    (Primrec.pair
      (horizontalOccurrenceVariableSourceComputed_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
    (variableSiteOccurrenceSlot_primrec.comp Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
