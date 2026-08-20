/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteComputability
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-! # Computability of horizontal occurrence-route preprocessing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceUnitSourceRouteComputed_primrec :
    Primrec horizontalOccurrenceUnitSourceRouteComputed := by
  exact
    PeriodicThreeDM.NormalizationCompiler.unitSubdividePolyline_primrec.comp
      horizontalOccurrenceSourceRouteComputed_primrec

theorem horizontalOccurrenceSourceVariableDirectionComputed_primrec :
    Primrec horizontalOccurrenceSourceVariableDirectionComputed := by
  exact
    PeriodicThreeDM.NormalizationCompiler.polylineFirstDirection_primrec.comp
      horizontalOccurrenceUnitSourceRouteComputed_primrec

theorem horizontalOccurrenceSourceClauseDirectionComputed_primrec :
    Primrec horizontalOccurrenceSourceClauseDirectionComputed := by
  exact
    PeriodicThreeDM.NormalizationCompiler.polylineLastDirection_primrec.comp
      horizontalOccurrenceUnitSourceRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
