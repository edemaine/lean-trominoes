/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRouteQueryInputComputability

/-! # Computability of selected horizontal occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceStoredRouteComputed_primrec :
    Primrec horizontalOccurrenceStoredRouteComputed := by
  exact horizontalRoutedRoutesComputed_primrec.comp
    horizontalOccurrenceRouteQueryInput_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
