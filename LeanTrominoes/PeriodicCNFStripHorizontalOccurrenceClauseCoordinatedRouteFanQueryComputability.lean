/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteMetadataComputability

/-! # Computability of clause coordinated-route fan queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseRibbonFanQueryComputed_primrec :
    Primrec horizontalOccurrenceClauseRibbonFanQueryComputed := by
  exact Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    (horizontalOccurrenceClauseIndexComputed_primrec.comp Primrec.fst)

end PeriodicCNFStripReduction
end LeanTrominoes
