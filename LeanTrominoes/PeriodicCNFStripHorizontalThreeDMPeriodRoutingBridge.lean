/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMPeriodBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRoutingSemanticBridge

/-! # The executable horizontal period is the routing period -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMPeriodComputed_eq_routing
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    horizontalThreeDMPeriodComputed source =
      (coordinatedSourceRibbonThreeStrandRouting
        (horizontalSemanticNormalizedRibbonReadyPresentation source)
        width compatible).period := by
  rw [horizontalThreeDMPeriodComputed_eq_semantic]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
