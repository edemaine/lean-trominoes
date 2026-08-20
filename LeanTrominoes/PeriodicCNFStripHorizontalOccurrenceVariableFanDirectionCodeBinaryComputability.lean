/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionCodeAtComputability

/-! # Binary computability of variable-fan direction codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonDirectionCodeComputed_primrec₂ :
    Primrec₂ fun
      (input : HorizontalVariableRibbonFanInput) (slot : VariableSiteSlot) =>
        axisDirectionEquivFin
          (horizontalOccurrenceVariableRibbonDirectionComputed input slot) :=
  horizontalOccurrenceVariableRibbonDirectionCodeAt_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
