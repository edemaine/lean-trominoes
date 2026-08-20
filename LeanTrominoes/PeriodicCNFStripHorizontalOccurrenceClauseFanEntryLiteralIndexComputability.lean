/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryLookupComputability

/-! # Computability of literal indices at proof-erased clause entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryLiteralIndexComputed_primrec :
    Primrec horizontalOccurrenceClauseEntryLiteralIndexComputed := by
  have selected : Primrec fun input :
      (HorizontalClauseRibbonFanInput ×
        HorizontalClauseOccurrenceEntry) × TaggedOccurrence RoutedVariable =>
      input.2.2.2 :=
    (Primrec.snd.comp Primrec.snd).comp Primrec.snd
  exact (Primrec.option_casesOn
    horizontalOccurrenceClauseEntryLookupComputed_primrec
    (Primrec.const 0) selected.to₂).of_eq fun input => by
      cases found : horizontalOccurrenceClauseEntryLookupComputed input <;>
        simp [horizontalOccurrenceClauseEntryLiteralIndexComputed, found]

end PeriodicCNFStripReduction
end LeanTrominoes
