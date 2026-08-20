/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteAtTagDataBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticRouteAtTagAssembledBridge

/-! # Semantic bridge for tag-indexed horizontal routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalAssembledRouteAtTagComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (tag : PeriodicThreeDM.IncidenceTag) :
    horizontalAssembledRouteAtTagComputed (source, tag) =
      @assembledRouteAtTag
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        tag :=
  (horizontalAssembledRouteAtTagComputed_eq_semanticData source tag).trans
    (horizontalSemanticAssembledRouteAtTagData_eq_assembled
      source width compatible tag)

end PeriodicCNFStripReduction
end LeanTrominoes
