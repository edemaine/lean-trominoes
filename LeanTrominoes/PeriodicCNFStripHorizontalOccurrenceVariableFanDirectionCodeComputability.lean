/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionCodesListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionCodesTripleComputability

/-! # Computability of variable-fan direction codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonDirectionsCodeComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonDirectionsCodeComputed := by
  exact horizontalOccurrenceVariableRibbonDirectionCodesTriple_primrec.comp
    horizontalOccurrenceVariableRibbonDirectionCodesListComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
