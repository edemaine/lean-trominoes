/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData

/-! # Computability of normalized occurrence lookup inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRouteSource_primrec :
    Primrec fun input : HorizontalOccurrenceRouteInput =>
      input.1.1 :=
  Primrec.fst.comp Primrec.fst

theorem horizontalOccurrenceLookupInput_primrec :
    Primrec horizontalOccurrenceLookupInput := by
  have formula : Primrec fun input : HorizontalOccurrenceRouteInput =>
      (horizontalNormalizedRoutedFormulaComputed input.1.1).erase :=
    PositionedPeriodicCNF.erase_primrec.comp
      (horizontalNormalizedRoutedFormulaComputed_primrec.comp
        horizontalOccurrenceRouteSource_primrec)
  exact Primrec.pair
    (Primrec.pair formula (Primrec.snd.comp Primrec.fst))
    Primrec.snd

end PeriodicCNFStripReduction
end LeanTrominoes
