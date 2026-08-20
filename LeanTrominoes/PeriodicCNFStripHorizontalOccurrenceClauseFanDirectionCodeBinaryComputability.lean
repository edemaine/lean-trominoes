/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDirectionComputability

/-! # Binary computability of clause-fan direction codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseDirectionCodeComputed_primrec₂ :
    Primrec₂ fun
      (input : HorizontalClauseRibbonFanInput)
      (group : X3CClauseTerminalGroup) =>
        axisDirectionEquivFin
          (horizontalOccurrenceClauseDirectionComputed input group) := by
  have encode : Primrec axisDirectionEquivFin :=
    Computability.finiteDomain_primrec _
  exact encode.comp₂ horizontalOccurrenceClauseDirectionComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
