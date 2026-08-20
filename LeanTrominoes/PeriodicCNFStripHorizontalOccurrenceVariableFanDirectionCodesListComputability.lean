/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionCodeBinaryComputability

/-! # Computability of the variable-fan direction-code list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonDirectionCodesListComputed_primrec :
    Primrec
      horizontalOccurrenceVariableRibbonDirectionCodesListComputed := by
  exact Primrec.list_map
    (Primrec.const
      ([.first, .second, .third] : List VariableSiteSlot))
    horizontalOccurrenceVariableRibbonDirectionCodeComputed_primrec₂

end PeriodicCNFStripReduction
end LeanTrominoes
