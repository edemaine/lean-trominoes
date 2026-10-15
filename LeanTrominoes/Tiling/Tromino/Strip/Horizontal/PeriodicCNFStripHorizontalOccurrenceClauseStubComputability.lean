/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseStubData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceSourceRouteComputability
import LeanTrominoes.Graphs.Drawings.Orthogonal.PolylineDefaultEndpointsComputability
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellComputability
import LeanTrominoes.Graphs.Drawings.Orthogonal.Construction.PeriodicOrthocrossingConstructionComputability

/-! # Computability of translated clause occurrence stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseCenterComputed_primrec :
    Primrec horizontalOccurrenceClauseCenterComputed := by
  exact polylineLastD_primrec.comp
    horizontalOccurrenceSourceRouteComputed_primrec

theorem horizontalOccurrenceClauseOriginComputed_primrec :
    Primrec fun input : HorizontalOccurrenceColoredRouteInput =>
      ribbonMacrocellOrigin
        (horizontalOccurrenceClauseCenterComputed input.1) := by
  exact ribbonMacrocellOrigin_primrec.comp
    (horizontalOccurrenceClauseCenterComputed_primrec.comp Primrec.fst)

theorem horizontalOccurrenceClauseStubComputed_primrec :
    Primrec horizontalOccurrenceClauseStubComputed := by
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp
    horizontalOccurrenceClauseOriginComputed_primrec
    horizontalOccurrenceClauseCoordinatedRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
