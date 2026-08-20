/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticAssembledRouteAtTagData
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceRouteSemanticBridge

/-! # Shallow semantic tag lookup agrees with certified assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalSemanticAssembledRouteAtTagData_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (tag : PeriodicThreeDM.IncidenceTag) :
    horizontalSemanticAssembledRouteAtTagData source tag =
      @assembledRouteAtTag
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        tag := by
  unfold horizontalSemanticAssembledRouteAtTagData
    horizontalSemanticThreeDMTypedTriples
  apply typedRouteAtTagListData_eq_assembled
  intro triple color
  exact horizontalTypedIncidenceRouteComputed_eq_assembled
    source width compatible triple color

end PeriodicCNFStripReduction
end LeanTrominoes
