/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRouteTableRowComputability
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntriesComputability

/-! # Computability of all colored occurrence queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceEntriesComputed_primrec :
    Primrec horizontalOccurrenceEntriesComputed := by
  exact occurrenceEntries_primrec.comp
    (PositionedPeriodicCNF.erase_primrec.comp
      horizontalNormalizedRoutedFormulaComputed_primrec)

theorem horizontalOccurrenceColoredInputsComputed_primrec :
    Primrec horizontalOccurrenceColoredInputsComputed := by
  exact Primrec.list_flatMap
    horizontalOccurrenceEntriesComputed_primrec
    horizontalOccurrenceColoredInputRowComputed_primrec.to₂

end PeriodicCNFStripReduction
end LeanTrominoes
