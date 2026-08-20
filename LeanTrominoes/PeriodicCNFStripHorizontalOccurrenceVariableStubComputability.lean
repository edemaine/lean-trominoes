/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellComputability
import LeanTrominoes.PeriodicOrthocrossingConstructionComputability

/-! # Computability of translated variable occurrence stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableCenterComputed_primrec :
    Primrec fun input : HorizontalOccurrenceColoredRouteInput =>
      horizontalPaddedRoutedPositionComputed input.1.1.1 input.1.1.2 := by
  exact horizontalPaddedRoutedPositionComputed_primrec.comp
    (Primrec.fst.comp Primrec.fst)

theorem horizontalOccurrenceVariableOriginComputed_primrec :
    Primrec fun input : HorizontalOccurrenceColoredRouteInput =>
      ribbonMacrocellOrigin
        (horizontalPaddedRoutedPositionComputed input.1.1.1 input.1.1.2) := by
  exact ribbonMacrocellOrigin_primrec.comp
    horizontalOccurrenceVariableCenterComputed_primrec

theorem horizontalOccurrenceVariableStubComputed_primrec :
    Primrec horizontalOccurrenceVariableStubComputed := by
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp
    horizontalOccurrenceVariableOriginComputed_primrec
    horizontalOccurrenceVariableCoordinatedRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
