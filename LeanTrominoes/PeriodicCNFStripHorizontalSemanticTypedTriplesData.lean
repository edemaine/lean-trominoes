/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes

/-! # Shallow semantic typed-triple data for the horizontal source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRibbonRoutedVariableDecidableEq

/-- Proof-backed typed triples under a shallow name for tag lookup. -/
def horizontalSemanticThreeDMTypedTriples
    (source : PeriodicCNF Nat) : List (Triple RoutedVariable) :=
  @triples RoutedVariable horizontalRibbonRoutedVariableDecidableEq
    (horizontalSemanticNormalizedRibbonSource source).erase

end PeriodicCNFStripReduction
end LeanTrominoes
