/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRouteTableInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteComputability

/-! # Computability of the complete colored occurrence-route table -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRouteTableComputed_primrec :
    Primrec horizontalOccurrenceRouteTableComputed := by
  have route : Primrec₂ fun (_source : PeriodicCNF Nat)
      (input : HorizontalOccurrenceColoredRouteInput) =>
      horizontalOccurrenceCoordinatedRouteComputed input :=
    (horizontalOccurrenceCoordinatedRouteComputed_primrec.comp
      Primrec.snd).to₂
  exact Primrec.list_map
    horizontalOccurrenceColoredInputsComputed_primrec route

end PeriodicCNFStripReduction
end LeanTrominoes
