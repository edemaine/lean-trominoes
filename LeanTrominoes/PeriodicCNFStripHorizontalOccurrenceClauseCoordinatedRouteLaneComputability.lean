/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteLaneInputComputability

/-! # Computability of clause coordinated-route lanes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : Inhabited WireColor := ⟨.red⟩

private theorem clauseRibbonLaneForColor_primrec :
    Primrec fun input : X3CClauseTerminalGroup × WireColor =>
      clauseRibbonLaneForColor input.1 input.2 :=
  Computability.finiteDomain_primrec _

theorem horizontalOccurrenceRibbonLaneComputed_primrec :
    Primrec horizontalOccurrenceRibbonLaneComputed := by
  exact clauseRibbonLaneForColor_primrec.comp
    horizontalOccurrenceRibbonLaneInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
