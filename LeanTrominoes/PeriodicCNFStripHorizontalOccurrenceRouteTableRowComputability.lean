/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRouteTableData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-! # Computability of one colored occurrence-query row -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceColoredInputRowComputed_primrec :
    Primrec horizontalOccurrenceColoredInputRowComputed := by
  have sourceAtom : Primrec fun combined :
      (PeriodicCNF Nat × (RoutedVariable × OccurrenceSlot)) × WireColor =>
      (combined.1.1, combined.1.2.1) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have routeInput : Primrec fun combined :
      (PeriodicCNF Nat × (RoutedVariable × OccurrenceSlot)) × WireColor =>
      ((combined.1.1, combined.1.2.1), combined.1.2.2) :=
    Primrec.pair sourceAtom
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have one : Primrec₂ fun
      (input : PeriodicCNF Nat × (RoutedVariable × OccurrenceSlot))
      (color : WireColor) =>
      (((input.1, input.2.1), input.2.2), color) :=
    (Primrec.pair routeInput Primrec.snd).to₂
  exact Primrec.list_map (Primrec.const incidenceColors) one

end PeriodicCNFStripReduction
end LeanTrominoes
