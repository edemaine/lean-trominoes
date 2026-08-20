/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseStubData

/-! # Executable complete coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Complete proof-free coordinated colored occurrence route. -/
def horizontalOccurrenceCoordinatedRouteComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  joinAtEndpoint
    (joinAtEndpoint
      (horizontalOccurrenceVariableStubComputed input)
      (horizontalOccurrenceRibbonCorridorCoreComputed input))
    (horizontalOccurrenceClauseStubComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes
