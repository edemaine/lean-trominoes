/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryGroupComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseRibbonFanDataEncoding

/-! # Computability of clause-terminal entry matching -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryMatchesGroupComputed_primrec₂ :
    Primrec₂ fun
      (input : HorizontalClauseRibbonGroupInput)
      (entry : HorizontalClauseOccurrenceEntry) =>
        horizontalOccurrenceClauseEntryMatchesGroupComputed (input, entry) := by
  change Primrec horizontalOccurrenceClauseEntryMatchesGroupComputed
  have group : Primrec fun data :
      HorizontalClauseRibbonGroupInput ×
        HorizontalClauseOccurrenceEntry =>
      horizontalOccurrenceClauseEntryGroupComputed
        (data.1.1, data.2) :=
    horizontalOccurrenceClauseEntryGroupComputed_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have equal : PrimrecPred fun data :
      HorizontalClauseRibbonGroupInput ×
        HorizontalClauseOccurrenceEntry =>
      horizontalOccurrenceClauseEntryGroupComputed
          (data.1.1, data.2) = data.1.2 :=
    Primrec.eq.comp group (Primrec.snd.comp Primrec.fst)
  exact equal.decide.of_eq fun data => by
    rfl

end PeriodicCNFStripReduction
end LeanTrominoes
