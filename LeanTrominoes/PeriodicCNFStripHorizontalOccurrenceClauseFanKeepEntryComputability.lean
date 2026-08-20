/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryClauseIndexComputability

/-! # Computability of clause-orbit entry filtering -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseKeepEntryComputed_primrec₂ :
    Primrec₂ fun
      (input : HorizontalClauseRibbonFanInput)
      (entry : HorizontalClauseOccurrenceEntry) =>
        if horizontalOccurrenceClauseEntryClauseIndexComputed
            (input, entry) = input.2 then
          some entry
        else
          none := by
  have selected : PrimrecPred fun data :
      HorizontalClauseRibbonFanInput × HorizontalClauseOccurrenceEntry =>
        horizontalOccurrenceClauseEntryClauseIndexComputed data =
          data.1.2 :=
    Primrec.eq.comp
      horizontalOccurrenceClauseEntryClauseIndexComputed_primrec
      (Primrec.snd.comp Primrec.fst)
  exact Primrec.ite selected
    (Primrec.option_some.comp Primrec.snd)
    (Primrec.const none)

end PeriodicCNFStripReduction
end LeanTrominoes
