/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionComputability

/-! # Computability of one variable-fan direction code -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonDirectionCodeAt_primrec :
    Primrec fun input :
        HorizontalVariableRibbonFanInput × VariableSiteSlot =>
      axisDirectionEquivFin
        (horizontalOccurrenceVariableRibbonDirectionComputed
          input.1 input.2) := by
  have encode : Primrec axisDirectionEquivFin :=
    Computability.finiteDomain_primrec _
  exact encode.comp
    horizontalOccurrenceVariableRibbonDirectionComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
