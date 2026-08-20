/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSourceComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntriesComputability

/-! # Computability of all normalized clause-fan occurrence entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseAllEntriesComputed_primrec :
    Primrec fun input : HorizontalClauseRibbonFanInput =>
      occurrenceEntries (horizontalOccurrenceClauseSourceComputed input) :=
  occurrenceEntries_primrec.comp
    horizontalOccurrenceClauseSourceComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
