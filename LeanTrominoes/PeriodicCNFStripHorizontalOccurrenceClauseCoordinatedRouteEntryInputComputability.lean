/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteData

/-! # Computability of clause coordinated-route entry repackaging -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseFanEntryInputComputed_primrec :
    Primrec horizontalOccurrenceClauseFanEntryInputComputed := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.const 0))
    (Primrec.pair
      (Primrec.snd.comp Primrec.fst)
      Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
