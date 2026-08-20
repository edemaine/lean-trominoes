/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDirectionSomeInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteComputability

/-! # Computability of found clause-fan directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseDirectionSomeComputed_primrec :
    Primrec fun input :
        HorizontalClauseRibbonGroupInput × HorizontalClauseOccurrenceEntry =>
      horizontalOccurrenceSourceClauseDirectionComputed
        ((input.1.1.1, input.2.1), input.2.2) :=
  horizontalOccurrenceSourceClauseDirectionComputed_primrec.comp
    horizontalOccurrenceClauseDirectionSomeInput_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
