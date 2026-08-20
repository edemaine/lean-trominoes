/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledEdgeRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticTypedTriplesData

/-! # Semantic bridge for horizontal typed-triple enumeration -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMTypedTriplesComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalThreeDMTypedTriplesComputed source =
      horizontalSemanticThreeDMTypedTriples source := by
  unfold horizontalThreeDMTypedTriplesComputed
    horizontalSemanticThreeDMTypedTriples
  rw [horizontalNormalizedRoutedEraseComputed_eq_semanticData]

end PeriodicCNFStripReduction
end LeanTrominoes
