/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonSemanticData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceSourceRouteData

/-! # Proof-free semantic occurrence-route data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The generic proof-free occurrence route instantiated with the exact
source, placement, and route family of the semantic ribbon presentation. -/
def horizontalSemanticOccurrenceSourceRouteData
    (input : HorizontalOccurrenceRouteInput) : List Cell :=
  occurrenceSourceRouteFromData
    (horizontalSemanticNormalizedRibbonSource input.1.1)
    ((horizontalSemanticRoutedPlacement input.1.1).scale 2)
    (PositionedPeriodicCNF.scaleIncidenceRoutes 2
      (horizontalSemanticRoutedRoutes input.1.1))
    (input.1.2, input.2)

end PeriodicCNFStripReduction
end LeanTrominoes
