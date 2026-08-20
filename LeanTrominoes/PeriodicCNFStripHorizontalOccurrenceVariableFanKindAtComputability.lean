/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanKindValueAtComputability

/-! # Computability of one variable-fan connector-kind code -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonKindCodeAt_primrec :
    Primrec fun input => variableConnectorKindEquivFin
      (horizontalOccurrenceVariableRibbonKindComputed input) := by
  have encode : Primrec variableConnectorKindEquivFin :=
    Computability.finiteDomain_primrec _
  exact encode.comp horizontalOccurrenceVariableRibbonKindComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
