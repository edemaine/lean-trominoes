/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMPeriodRoutingBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMEdgeRoutesSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMAssembledDrawingDataBridge

/-! # Identification of the executable and assembled horizontal drawings -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMDrawingComputed_gridSizePred_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    (horizontalThreeDMDrawingComputed source).gridSizePred =
      (coordinatedSourceRibbonThreeStrandRouting
        (horizontalSemanticNormalizedRibbonReadyPresentation source)
        width compatible).period - 1 := by
  rw [horizontalThreeDMDrawingComputed_gridSizePred]
  unfold horizontalThreeDMGridSizePredComputed
  exact congrArg (fun period : Nat => period - 1)
    (horizontalThreeDMPeriodComputed_eq_routing source width compatible)

theorem horizontalThreeDMDrawingComputed_vertexPositions_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    (horizontalThreeDMDrawingComputed source).vertexPositions =
      @assembledVertexPositions
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible) := by
  rw [horizontalThreeDMDrawingComputed_vertexPositions]
  exact horizontalThreeDMVertexPositionsComputed_eq_semantic
    source width compatible

theorem horizontalThreeDMDrawingComputed_edgeRoutes_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    (horizontalThreeDMDrawingComputed source).edgeRoutes =
      @assembledEdgeRoutes
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible) := by
  rw [horizontalThreeDMDrawingComputed_edgeRoutes]
  exact horizontalThreeDMEdgeRoutesComputed_eq_assembled
    source width compatible

theorem horizontalThreeDMDrawingComputed_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    horizontalThreeDMDrawingComputed source =
      @assembledDrawing
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible) := by
  apply eq_assembledDrawing_of_fields
  · exact horizontalThreeDMDrawingComputed_gridSizePred_eq_assembled
      source width compatible
  · exact horizontalThreeDMDrawingComputed_vertexPositions_eq_assembled
      source width compatible
  · exact horizontalThreeDMDrawingComputed_edgeRoutes_eq_assembled
      source width compatible

end PeriodicCNFStripReduction
end LeanTrominoes
