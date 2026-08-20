/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData

/-! # Computability of proof-erased clause-entry queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryQueryComputed_primrec :
    Primrec horizontalOccurrenceClauseEntryQueryComputed := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
