/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseComputability
import LeanTrominoes.PeriodicCNFGaugeComputability

/-! # Computability of horizontal occurrence-route rebasing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceTranslationComputed_primrec :
    Primrec horizontalOccurrenceTranslationComputed := by
  have period : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      horizontalPaddedRoutedPeriodComputed input.1.1.1 :=
    horizontalPaddedRoutedPeriodComputed_primrec.comp
      horizontalOccurrenceRouteSomeSource_primrec
  have factor : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      (horizontalPaddedRoutedPeriodComputed input.1.1.1 : Int) :=
    Computability.int_ofNat_primrec.comp period
  have anchor : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      PeriodicCNF.clauseAnchor
        (horizontalOccurrenceClauseComputed input) :=
    PeriodicCNF.clauseAnchor_primrec.comp
      horizontalOccurrenceClauseComputed_primrec
  have offset : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      input.2.1.offset :=
    PeriodicThreeCNF.literal_offset_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have displacement : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      Cell.sub
        (PeriodicCNF.clauseAnchor
          (horizontalOccurrenceClauseComputed input))
        input.2.1.offset :=
    Computability.cell_sub_primrec.comp anchor offset
  exact (Computability.cell_scale_primrec.comp
    factor displacement).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
