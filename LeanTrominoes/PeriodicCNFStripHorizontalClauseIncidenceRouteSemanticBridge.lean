/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMOriginSemanticBridge

/-! # Semantic bridge for translated horizontal clause routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalClauseIncidenceRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (clauseIndex : Nat) (set : PlanarThreeDM.X3CClauseSet)
    (color : WireColor) :
    horizontalClauseIncidenceRouteComputed
        (((source, clauseIndex), set), color) =
      assembledClauseRoute
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        clauseIndex set color := by
  unfold horizontalClauseIncidenceRouteComputed assembledClauseRoute
  rw [horizontalThreeDMClauseOriginComputed_eq_routing]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
