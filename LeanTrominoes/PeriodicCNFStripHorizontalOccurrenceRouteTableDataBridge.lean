/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRouteTableData

/-! # Row form of the executable colored occurrence-route table -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRouteTableComputed_eq_rows
    (source : PeriodicCNF Nat) :
    horizontalOccurrenceRouteTableComputed source =
      (horizontalOccurrenceEntriesComputed source).flatMap fun entry =>
        incidenceColors.map fun color =>
          horizontalOccurrenceCoordinatedRouteComputed
            (((source, entry.1), entry.2), color) := by
  simp [horizontalOccurrenceRouteTableComputed,
    horizontalOccurrenceColoredInputsComputed,
    horizontalOccurrenceColoredInputRowComputed,
    List.map_flatMap, List.map_map, Function.comp_def]

end PeriodicCNFStripReduction
end LeanTrominoes
