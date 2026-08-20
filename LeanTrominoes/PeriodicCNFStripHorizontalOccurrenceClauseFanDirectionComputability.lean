/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSelectedEntryComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDirectionSomeComputability
import LeanTrominoes.AxisDirectionComputability

/-! # Computability of clause-fan endpoint directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseDirectionComputed_primrec :
    Primrec₂ horizontalOccurrenceClauseDirectionComputed := by
  change Primrec fun input : HorizontalClauseRibbonGroupInput =>
    horizontalOccurrenceClauseDirectionComputed input.1 input.2
  exact (Primrec.option_casesOn
    horizontalOccurrenceClauseSelectedEntryComputed_primrec
    (Primrec.const AxisDirection.north)
    horizontalOccurrenceClauseDirectionSomeComputed_primrec.to₂).of_eq
      fun input => by
        cases found : horizontalOccurrenceClauseSelectedEntryComputed input <;>
          simp [horizontalOccurrenceClauseDirectionComputed, found]

end PeriodicCNFStripReduction
end LeanTrominoes
