/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntriesComputability
import LeanTrominoes.PeriodicThreeDMGraph

/-! # Executable finite table of colored occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PeriodicThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Proof-free active occurrence pairs of the normalized routed source. -/
def horizontalOccurrenceEntriesComputed
    (source : PeriodicCNF Nat) : List (RoutedVariable × OccurrenceSlot) :=
  occurrenceEntries
    (horizontalNormalizedRoutedFormulaComputed source).erase

/-- The three route queries attached to one proof-free active occurrence. -/
def horizontalOccurrenceColoredInputRowComputed
    (input : PeriodicCNF Nat × (RoutedVariable × OccurrenceSlot)) :
    List HorizontalOccurrenceColoredRouteInput :=
  incidenceColors.map fun color =>
    (((input.1, input.2.1), input.2.2), color)

/-- All colored occurrence queries in the stable normalized-source order. -/
def horizontalOccurrenceColoredInputsComputed
    (source : PeriodicCNF Nat) :
    List HorizontalOccurrenceColoredRouteInput :=
  (horizontalOccurrenceEntriesComputed source).flatMap
    fun entry =>
      horizontalOccurrenceColoredInputRowComputed (source, entry)

/-- Complete coordinated route for every normalized occurrence and color. -/
def horizontalOccurrenceRouteTableComputed
    (source : PeriodicCNF Nat) : List (List Cell) :=
  (horizontalOccurrenceColoredInputsComputed source).map
    horizontalOccurrenceCoordinatedRouteComputed

end PeriodicCNFStripReduction
end LeanTrominoes
