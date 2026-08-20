/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceScaledRouteComputability

/-! # Computability of reversed horizontal occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceReversedRouteComputed_primrec :
    Primrec horizontalOccurrenceReversedRouteComputed := by
  exact Primrec.list_reverse.comp
    horizontalOccurrenceScaledRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
