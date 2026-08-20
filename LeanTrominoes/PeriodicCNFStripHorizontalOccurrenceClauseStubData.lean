/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData
import LeanTrominoes.PolylineDefaultEndpoints

/-! # Executable translated clause occurrence stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PeriodicOrthocrossing

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Lifted clause macrocell center recovered from the executable source
route. -/
def horizontalOccurrenceClauseCenterComputed
    (input : HorizontalOccurrenceRouteInput) : Cell :=
  polylineLastD (horizontalOccurrenceSourceRouteComputed input)

/-- Coordinated clause fan translated to its executable lifted target
macrocell. -/
def horizontalOccurrenceClauseStubComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  translatePolyline
    (ribbonMacrocellOrigin
      (horizontalOccurrenceClauseCenterComputed input.1))
    (horizontalOccurrenceClauseCoordinatedRouteComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes
