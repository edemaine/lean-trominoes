/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOrdinaryIncidenceRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalFixedRedIncidenceRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalClauseIncidenceRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticTypedTriplesData

/-! # Semantic bridge for complete horizontal typed incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalTypedIncidenceRouteComputed_eq_assembled
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (triple : {triple : Triple RoutedVariable //
      triple ∈ horizontalSemanticThreeDMTypedTriples source})
    (color : WireColor) :
    horizontalTypedIncidenceRouteComputed ((source, triple.1), color) =
      @assembledTypedIncidenceRoute
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        triple color := by
  rcases triple with ⟨triple, member⟩
  cases triple with
  | ordinary atom slot variant localTriple =>
      exact
        horizontalVariableTypedIncidenceRouteComputed_eq_assembledOrdinary
          source width compatible atom slot variant localTriple member color
  | fixedRed atom slot localTriple =>
      exact
        horizontalVariableTypedIncidenceRouteComputed_eq_assembledFixedRed
          source width compatible atom slot localTriple member color
  | clause clauseIndex set =>
      exact horizontalClauseIncidenceRouteComputed_eq_semantic
        source width compatible clauseIndex set color

end PeriodicCNFStripReduction
end LeanTrominoes
